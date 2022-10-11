import collections
import random
import string
from tkinter import StringVar, messagebox ,Text
from typing import List, Tuple
import sympy
import matplotlib.pyplot as plt
import numpy as np
import datetime


def inv(n, q):
    """div on PN modulo a/b mod q as a * inv(b, q) mod q
    >>> assert n * inv(n, q) % q == 1
    """
    # n*inv % q = 1 => n*inv = q*m + 1 => n*inv + q*-m = 1
    # => egcd(n, q) = (inv, -m, 1) => inv = egcd(n, q)[0] (mod q)
    return egcd(n, q)[0] % q


def egcd(a, b):
    """extended GCD
    returns: (s, t, gcd) as a*s + b*t == gcd
    >>> s, t, gcd = egcd(a, b)
    >>> assert a % gcd == 0 and b % gcd == 0
    >>> assert a * s + b * t == gcd
    """
    s0, s1, t0, t1 = 1, 0, 0, 1
    while b > 0:
        q, r = divmod(a, b)
        a, b = b, r
        s0, s1, t0, t1 = s1, s0 - q * s1, t1, t0 - q * t1
        pass
    return s0, t0, a


def sqrt(n, q):
    """sqrt on PN modulo: returns two numbers or exception if not exist
    >>> assert (sqrt(n, q)[0] ** 2) % q == n
    >>> assert (sqrt(n, q)[1] ** 2) % q == n
    """
    assert n < q
    for i in range(1, q):
        if i * i % q == n:
            return (i, q - i)
        pass
    raise Exception("not found")


Coord = collections.namedtuple("Coord", ["x", "y"])


class EC(object):
    """System of Elliptic Curve"""

    def __init__(self, a, b, q):
        """elliptic curve as: (y**2 = x**3 + a * x + b) mod q
        - a, b: params of curve formula
        - q: prime number
        """
        assert 0 < a and a < q and 0 < b and b < q and q > 2
        self.a = a
        self.b = b
        self.q = q
        # just as unique ZERO value representation for "add": (not on curve)
        self.zero = Coord(0, 0)
        pass

    def is_valid(self, p):
        if p == self.zero: return True
        l = (p.y ** 2) % self.q
        r = ((p.x ** 3) + self.a * p.x + self.b) % self.q
        return l == r

    def at(self, x):
        """find points on curve at x
        - x: int < q
        - returns: ((x, y), (x,-y)) or not found exception
        >>> a, ma = ec.at(x)
        >>> assert a.x == ma.x and a.x == x
        >>> assert a.x == ma.x and a.x == x
        >>> assert ec.neg(a) == ma
        >>> assert ec.is_valid(a) and ec.is_valid(ma)
        """
        assert x < self.q
        ysq = (x ** 3 + self.a * x + self.b) % self.q
        y, my = sqrt(ysq, self.q)
        return Coord(x, y), Coord(x, my)

    def neg(self, p):
        """negate p
        >>> assert ec.is_valid(ec.neg(p))
        """
        return Coord(p.x, -p.y % self.q)

    def add(self, p1, p2):
        """<add> of elliptic curve: negate of 3rd cross point of (p1,p2) line
        >>> d = ec.add(a, b)
        >>> assert ec.is_valid(d)
        >>> assert ec.add(d, ec.neg(b)) == a
        >>> assert ec.add(a, ec.neg(a)) == ec.zero
        >>> assert ec.add(a, b) == ec.add(b, a)
        >>> assert ec.add(a, ec.add(b, c)) == ec.add(ec.add(a, b), c)
        """
        if p1 == self.zero: return p2
        if p2 == self.zero: return p1
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0):
            # p1 + -p1 == 0
            return self.zero
        if p1.x == p2.x:
            # p1 + p1: use tangent line of p1 as (p1,p1) line
            l = (3 * p1.x * p1.x + self.a) * inv(2 * p1.y, self.q) % self.q
            pass
        else:
            l = (p2.y - p1.y) * inv(p2.x - p1.x, self.q) % self.q
            pass
        x = (l * l - p1.x - p2.x) % self.q
        y = (l * (p1.x - x) - p1.y) % self.q
        return Coord(x, y)

    def mul(self, p, n):
        """n times <mul> of elliptic curve
        >>> m = ec.mul(p, n)
        >>> assert ec.is_valid(m)
        >>> assert ec.mul(p, 0) == ec.zero
        """
        r = self.zero
        m2 = p
        # O(log2(n)) add
        while 0 < n:
            if n & 1 == 1:
                r = self.add(r, m2)
                pass
            n, m2 = n >> 1, self.add(m2, m2)
            pass
        # [ref] O(n) add
        # for i in range(n):
        #    r = self.add(r, p)
        #    pass
        return r

    def order(self, g):
        """order of point g
        >>> o = ec.order(g)
        >>> assert ec.is_valid(a) and ec.mul(a, o) == ec.zero
        >>> assert o <= ec.q
        """
        assert self.is_valid(g) and g != self.zero
        for i in range(1, self.q + 1):
            if self.mul(g, i) == self.zero:
                return i
            pass
        raise Exception("Invalid order")

    pass


class ElGamal(object):
    """ElGamal Encryption
    pub key encryption as replacing (mulmod, powmod) to (ec.add, ec.mul)
    - ec: elliptic curve
    - g: (random) a point on ec
    """

    def __init__(self, ec, g):
        assert ec.is_valid(g)
        self.ec = ec
        self.g = g
        self.n = ec.order(g)
        pass

    def gen(self, priv):
        """generate pub key
        - priv: priv key as (random) int < ec.q
        - returns: pub key as points on ec
        """
        return self.ec.mul(self.g, priv)

    def enc(self, plain, pub, r):
        """encrypt
        - plain: data as a point on ec
        - pub: pub key as points on ec
        - r: randam int < ec.q
        - returns: (cipher1, ciper2) as points on ec
        """
        assert self.ec.is_valid(plain)
        assert self.ec.is_valid(pub)
        # return self.ec.mul(self.g, r), self.ec.add(plain, self.ec.mul(pub, r))
        return self.ec.add(plain, self.ec.mul(pub, r))


    def enc2(self, plain, pub, r):
        assert self.ec.is_valid(plain)
        assert self.ec.is_valid(pub)
        return (self.ec.mul(self.g, r), self.ec.add(plain, self.ec.mul(pub, r)))

    def dec(self, cipher, priv):
        """decrypt
        - chiper: (chiper1, chiper2) as points on ec
        - priv: private key as int < ec.q
        - returns: plain as a point on ec
        """
        c1, c2 = cipher
        assert self.ec.is_valid(c1) and self.ec.is_valid(c2)
        return self.ec.add(c2, self.ec.neg(self.ec.mul(c1, priv)))

    pass


def map_to_points_ascii(message: str, ec: EC) -> List[Tuple]:
    result = []
    for c in message:
        p, _ = ec.at(ord(c))
        result.append(p)
    return result


def map_to_point_koblitz(m: int, ec: EC):
    max_bits = 20
    for bit in range(1, max_bits):
        try:
            x = (m * max_bits + bit) % ec.q
            p, _ = ec.at(x)
            return p
        except:
            pass


def map_to_chars(points):
    max_bits = 20
    m=[]
    for point in points:
        m.append(round(int(point)/max_bits))
    plain_text=[]
    for char in range(len(m)):
        plain_text.append(m[char])
    res = ""
    for i in plain_text:
        res=res+ chr(i)

    return res



def map_to_points_koblitz(message: str, ec: EC) -> List[Tuple]:
    # only Upper Letters
    result = []
    for c in message:
        p = map_to_point_koblitz(ord(c), ec)
        result.append(p)
    return result


def encrypt_points(points, eg, pub, rand):
    return [eg.enc(p, pub, rand) for p in points]

def encrypt_points2(points,eg,pub,rand):
    return [eg.enc2(p,pub,rand)for p in points]


def upper_case_letters_validator(input):
    if input:
        return input.isalpha()
    return True

def number_validator(input):
    if input:
        return input.isnumeric()
    return True


def prime_validator(input: str, event: str) -> bool:
    if event == 'key':
        return number_validator(input)

    if event != 'focusout':
        return True

    if not input.isnumeric():
        return False

    prime = int(input)

    if sympy.isprime(prime):
        return True

    next_prime = sympy.nextprime(prime)
    messagebox.showerror('Invalid prime number', f'please enter a valid prime number suggested value for {prime} is {next_prime}')
    return False



def build_gui():
    import tkinter as tk
    parent = tk.Tk()
    parent.geometry("800x600")
    message_label = tk.Label(parent, text="Message").place(x=30, y=70)
    file_path_label = tk.Label(parent,text="encrypted file path").place(x=30,y=110)
    encoded_message_label = tk.Label(parent, text="Encoded Message").place(x=30, y=150)
    encrypted_message_label = tk.Label(parent, text="Encrypted Message").place(x=30, y=190)
    decrypted_points_label = tk.Label(parent,text ="Decrypted message").place(x=30,y=230)
    decrypted_message_label = tk.Label(parent,text ="Decrypted points").place(x=30,y=270)
    first_label = tk.Label(parent, text="first coefficient (a)").place(x=30, y=320)
    second_label = tk.Label(parent, text="second coefficient (b)").place(x=30, y=360)
    prime = tk.Label(parent, text="prime").place(x=30, y=410)
    private_key_lable = tk.Label(parent, text="private_key").place(x=30, y=460)
    tk.Label(parent, text="an example of the curve elements is (9,7,4093)").place(x=30, y=510)


    reg = parent.register(upper_case_letters_validator)
    reg2 = parent.register(number_validator)
    is_prime = parent.register(prime_validator)

    encoded_message = StringVar()
    encrypted_message = StringVar()
    decrypted_message = StringVar()
    decrypted_points = StringVar()
    first_coff = StringVar()
    second_coff = StringVar()
    prime_number = StringVar()
    private_key = StringVar()

    first_coff.set("9")
    second_coff.set("7")
    prime_number.set("4093")
    private_key.set("5")


    message_input = tk.Entry(parent, validate='key', validatecommand=(reg, '%P'))
    message_input.place(x=150, y=70)

    file_path_input = tk.Entry(parent,width=100)
    file_path_input.place(x=150,y=110)

    encoded_message_input = tk.Entry(parent, state='disabled', textvariable=encoded_message, width=100)
    encoded_message_input.place(x=150, y=150)

    encrypted_message_input = tk.Entry(parent, state='disabled', textvariable=encrypted_message, width=100)
    encrypted_message_input.place(x=150, y=190)

    decrypted_message_input = tk.Entry(parent, state='disabled', textvariable=decrypted_message, width=100)
    decrypted_message_input.place(x=150, y=230)

    decrypted_points_input = tk.Entry(parent, state='disabled', textvariable=decrypted_points, width=100)
    decrypted_points_input.place(x=150,y=270)

    first_input = tk.Entry(parent, validate='key', validatecommand=(reg2, '%P'), textvariable=first_coff)
    first_input.place(x=150, y=310)

    second_input = tk.Entry(parent, validate='key', validatecommand=(reg2, '%P'), textvariable=second_coff)
    second_input.place(x=150, y=360)

    prime_input = tk.Entry(parent, validate='all', validatecommand=(is_prime, '%P', '%V'), textvariable=prime_number)
    prime_input.place(x=150, y=410)

    private_key_input = tk.Entry(parent, validate='key', validatecommand=(reg2, '%P'), textvariable=private_key)
    private_key_input.place(x=150, y=460)


    points=tk.Text(parent, width = 20, height = 40, padx = 10,pady = 10,)
    points.place(x=300,y= 310)
    




    def set_points():
        temp = ""
        a = int(first_input.get())
        b = int(second_input.get())
        q = int(prime_input.get())
        ec = EC(a, b, q)

        temp = ''
        fig = plt.figure(figsize=(10, 5))

        for i in list(string.ascii_lowercase + string.ascii_uppercase + string.digits + ' '):
            coord = map_to_point_koblitz(ord(i), ec)
            plt.plot(coord[0], coord[1], marker="o", markersize=5, markeredgecolor="red", markerfacecolor="green")
            plt.annotate(i, (coord[0], coord[1]))
            temp = temp + i + ' is  ' + '(' + str(coord[0]) + ',' + str(coord[1]) + ')'+ '\n'


        plt.axhline()
        plt.axvline()
        print(temp)
        # Show the plot
        plt.show()
        points.insert('2.0' ,temp)
        return temp 

    def is_valid_eg():
        a = int(first_input.get())
        b = int(second_input.get())
        q = int(prime_input.get())
        return (4 * (a ** 3) + 27 * (b ** 2)) % q != 0

    def get_eg_g(q, ec):
        for i in range(q):
            try:
                g, _ = ec.at(i)
                assert ec.order(g) <= ec.q
                return g
            except Exception as e:
                pass


    def encrypt_message():
        if not is_valid_eg():
            messagebox.showerror('EC Error', 'EC is singular!')
            return None

        a = int(first_input.get())
        b = int(second_input.get())
        q = int(prime_input.get())
        ec = EC(a, b, q)

        g = get_eg_g(q, ec)
        if not g:
            messagebox.showerror('EG Error', 'EC is bad!')
            return None

        # ElGamal enc/dec usage
        eg = ElGamal(ec, g)

        message = message_input.get()
        points = map_to_points_koblitz(message, ec)
        encoded_message.set(points)
        priv = 5
        pub = eg.gen(priv)
        encrypted_message.set(encrypt_points2(points, eg, pub, 15))
        x= encrypt_points2(points, eg, pub, 15)

        file_name = message[0] +str(random.randint(100000,99999999999999))+'.txt'
        print(file_name)

        encrypted_string = encrypted_message.get()
        f = open(file_name, "w+")
        f.write(encrypted_string)








    def decrypt_message():
        if not is_valid_eg():
            messagebox.showerror('EC Error', 'EC is singular!')
            return None

        a = int(first_input.get())
        b = int(second_input.get())
        q = int(prime_input.get())
        ec = EC(a, b, q)
        priv = 5

        g = get_eg_g(q, ec)
        if not g:
            messagebox.showerror('EG Error', 'EC is bad!')
            return None

        eg = ElGamal(ec, g)
        path = file_path_input.get()
        path_with_extension = path+'.txt'
        f = open(path_with_extension, 'r')
        cipher_text = f.read()
        filtrered_cipher_text = ''
        for char in cipher_text:
            if not(char==')' or char=='(' or char==','):
                filtrered_cipher_text = filtrered_cipher_text + char

        cipher_list = filtrered_cipher_text.split()
        points = []
        for i in range(len(cipher_list)):
            if(i%4 == 0):
                x1 = int(cipher_list[i])
                y1 = int(cipher_list[i+1])
                x2 = int(cipher_list[i+2])
                y2 = int(cipher_list[i+3])
                coord1 = Coord(x1, y1)
                coord2 = Coord(x2, y2)
                ciphered_char = (coord1,coord2)
                points.append(ciphered_char)
        plain_points=[]
        for i in points:
            point = eg.dec(i,priv)
            plain_points.append(point)

        decrypted_points.set(plain_points)
        temp_points = []
        for i in plain_points:
            temp_points.append(str(i[0]))

        result = map_to_chars(temp_points)
        decrypted_message.set(result)




    def validate_coffs():
        a = int(first_input.get())
        b = int(second_input.get())
        q = int(prime_input.get())

        if not (4*(a**3) + 27*(b**2) %  q != 0):
            messagebox.showerror('bad coefficients', 'please enter other numbers beacause 4a^3+27b^2 mod prime is equal to zero please enter valid coefficients like 9 and 7  for example')
            return False

        return "all right"

    
        

    

    tk.Button(parent, text="Encrypt", activebackground="green", activeforeground="blue", command=encrypt_message).place(x=600, y=320)
    tk.Button(parent, text= "print points",activebackground="green", activeforeground="blue",command = set_points).place(x=600,y=360)
    tk.Button(parent, text="Decrypt", activebackground="green", activeforeground="blue", command=decrypt_message).place(x=600, y=400)
    tk.Button(parent,text="validate", activebackground="green", activeforeground="blue", command=validate_coffs).place(x=600, y=440)
    parent.mainloop()


if __name__ == "__main__":
    # ec = EC(9, 7, 4093)
    # for i in range(4093):
    #     try:
    #         print(f"Iter {i}")
    #         g, _ = ec.at(i)
    #         ec.order(g)
    #         print("Yes")
    #         print(i)
    #     except Exception as e:
    #         pass
    # g, _ = ec.at(22)
    # assert ec.order(g) <= ec.q

    # ElGamal enc/dec usage
    # eg = ElGamal(ec, g)
    # mapping value to ec point
    # "masking": value k to point ec.mul(g, k)
    # ("imbedding" on proper n:use a point of x as 0 <= n*v <= x < n*(v+1) < q)
    # mapping = [ec.mul(g, i) for i in range(eg.n)]
    # plain = mapping[7]
    #
    # priv = 5
    # pub = eg.gen(priv)

    # cipher = eg.enc(plain, pub, 15)
    # decoded = eg.dec(cipher, priv)
    


    build_gui()

    # assert decoded == plain
    # assert cipher != pub

