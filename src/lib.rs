use std::{
    fmt::Display,
    ops::{BitAnd, BitOr, BitXor, Index, Not},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitArray<const N: usize>(pub [usize; N]);

impl<const N: usize> BitArray<N> {
    pub fn new() -> Self {
        Self([0; N])
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        let chunk_ind = index / usize::BITS as usize;
        let bit_ind = index % usize::BITS as usize;

        let chunk = self.0.get(chunk_ind)?;

        Some((chunk >> bit_ind) & 1 != 0)
    }

    pub fn set(&mut self, index: usize, val: bool) {
        let chunk_ind = index / usize::BITS as usize;
        let bit_ind = index % usize::BITS as usize;

        if val {
            self.0[chunk_ind] |= 1 << bit_ind;
        } else {
            self.0[chunk_ind] &= !(1 << bit_ind);
        }
    }

    pub fn set_range(&mut self, from: usize, to: usize, val: bool) {
        let from_chunk_ind = from / usize::BITS as usize;
        let from_bit_ind = from % usize::BITS as usize;
        let to_chunk_ind = to / usize::BITS as usize;
        let to_bit_ind = to % usize::BITS as usize;

        if from_chunk_ind == to_chunk_ind {
            let n_bits = to - from;

            let mask =
                ((!0) >> (usize::BITS as usize - n_bits)) << from_bit_ind;

            if val {
                self.0[from_chunk_ind] |= mask;
            } else {
                self.0[from_chunk_ind] &= !mask;
            }
        } else {
            let mask = (!0) << from_bit_ind;

            if val {
                self.0[from_chunk_ind] |= mask;
            } else {
                self.0[from_chunk_ind] &= !mask;
            }

            for i in from_chunk_ind + 1..to_chunk_ind {
                if val {
                    self.0[i] = !0;
                } else {
                    self.0[i] = 0;
                }
            }

            let mask = (!0) >> (usize::BITS as usize - to_bit_ind);

            if val {
                self.0[to_chunk_ind] |= mask;
            } else {
                self.0[to_chunk_ind] &= !mask;
            }
        }
    }

    pub fn count_ones(&self) -> usize {
        self.0.into_iter().map(|x| x.count_ones() as usize).sum()
    }

    pub fn count_zeros(&self) -> usize {
        self.0.into_iter().map(|x| x.count_zeros() as usize).sum()
    }

    pub fn trailing_zeros(&self) -> usize {
        let mut ans = 0;

        for x in self.0 {
            if x == 0 {
                ans += usize::BITS as usize;
            } else {
                ans += x.trailing_zeros() as usize;
                break;
            }
        }

        ans
    }

    pub fn leading_zeros(&self) -> usize {
        let mut ans = 0;

        for x in self.0.into_iter().rev() {
            if x == 0 {
                ans += usize::BITS as usize;
            } else {
                ans += x.leading_zeros() as usize;
                break;
            }
        }

        ans
    }

    pub fn trues_iter(&self) -> BitArrayTruesIter<N> {
        BitArrayTruesIter {
            data: self.0,
            chunk_ind: 0,
            cur_chunk: self.0[0],
            left_of_chunk: usize::BITS,
            total_ind: 0,
        }
    }

    pub fn nbits_iter<const NBITS: u32>(&self) -> BitArrayNBitsIter<N, NBITS> {
        BitArrayNBitsIter {
            data: self.0,
            chunk_ind: 0,
            cur_chunk: self.0[0],
            left_of_chunk: usize::BITS / NBITS,
        }
    }

    pub fn get_nbit<const NBITS: u32>(&self, i: usize) -> usize {
        assert_eq!(usize::BITS % NBITS, 0);

        let n_in_chunk = usize::BITS / NBITS;

        let chunk_ind = i / n_in_chunk as usize;
        let sub_ind = (i % n_in_chunk as usize) as u32;

        let chunk = self.0[chunk_ind];

        let mask = (!0) >> (usize::BITS - NBITS);

        (chunk >> (sub_ind * NBITS)) & mask
    }

    pub fn set_nbit<const NBITS: u32>(&mut self, i: usize, val: usize) {
        assert_eq!(usize::BITS % NBITS, 0);

        let n_in_chunk = usize::BITS / NBITS;

        let chunk_ind = i / n_in_chunk as usize;
        let sub_ind = (i % n_in_chunk as usize) as u32;

        let mask = ((!0) >> (usize::BITS - NBITS)) << (sub_ind * NBITS);

        let chunk = self.0[chunk_ind];

        self.0[chunk_ind] = (chunk & !mask) | (val << (sub_ind * NBITS));
    }
}

impl<const N: usize> Default for BitArray<N> {
    fn default() -> Self {
        Self([0; N])
    }
}

impl<const N: usize> Index<usize> for BitArray<N> {
    type Output = bool;

    fn index(&self, index: usize) -> &Self::Output {
        if self.get(index).unwrap() {
            &true
        } else {
            &false
        }
    }
}

impl<const N: usize> BitOr for BitArray<N> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        let mut new_bits = [0; N];

        for ((a, b), x) in
            self.0.into_iter().zip(rhs.0.into_iter()).zip(&mut new_bits)
        {
            *x = a | b;
        }

        Self(new_bits)
    }
}

impl<const N: usize> BitAnd for BitArray<N> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        let mut new_bits = [0; N];

        for ((a, b), x) in
            self.0.into_iter().zip(rhs.0.into_iter()).zip(&mut new_bits)
        {
            *x = a & b;
        }

        Self(new_bits)
    }
}

impl<const N: usize> BitXor for BitArray<N> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        let mut new_bits = [0; N];

        for ((a, b), x) in
            self.0.into_iter().zip(rhs.0.into_iter()).zip(&mut new_bits)
        {
            *x = a ^ b;
        }

        Self(new_bits)
    }
}

impl<const N: usize> Not for BitArray<N> {
    type Output = Self;

    fn not(self) -> Self {
        Self(self.0.map(|x| !x))
    }
}

pub struct BitArrayIter<const N: usize> {
    data: [usize; N],
    chunk_ind: usize,
    cur_chunk: usize,
    left_of_chunk: u32,
}

impl<const N: usize> Iterator for BitArrayIter<N> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.left_of_chunk == 0 {
            self.chunk_ind += 1;
            self.cur_chunk = *self.data.get(self.chunk_ind)?;
            self.left_of_chunk = usize::BITS;
        }

        self.left_of_chunk -= 1;
        let bit = (self.cur_chunk & 1) != 0;
        self.cur_chunk >>= 1;

        Some(bit)
    }
}

impl<const N: usize> IntoIterator for BitArray<N> {
    type Item = bool;

    type IntoIter = BitArrayIter<N>;

    fn into_iter(self) -> Self::IntoIter {
        BitArrayIter {
            data: self.0,
            chunk_ind: 0,
            cur_chunk: self.0[0],
            left_of_chunk: usize::BITS,
        }
    }
}

impl<const N: usize> Display for BitArray<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for bit in *self {
            write!(f, "{}", if bit { '1' } else { '0' })?;
        }

        Ok(())
    }
}

pub struct BitArrayTruesIter<const N: usize> {
    data: [usize; N],
    cur_chunk: usize,
    chunk_ind: usize,
    left_of_chunk: u32,
    total_ind: usize,
}

impl<const N: usize> Iterator for BitArrayTruesIter<N> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while self.cur_chunk == 0 {
            self.chunk_ind += 1;
            self.cur_chunk = *self.data.get(self.chunk_ind)?;
            self.total_ind += self.left_of_chunk as usize;
            self.left_of_chunk = usize::BITS;
        }

        let shifter = self.cur_chunk.trailing_zeros();
        self.cur_chunk = (self.cur_chunk >> shifter) & !1;
        self.total_ind += shifter as usize;
        self.left_of_chunk -= shifter;

        Some(self.total_ind)
    }
}

pub struct BitArrayNBitsIter<const N: usize, const NBITS: u32> {
    data: [usize; N],
    chunk_ind: usize,
    cur_chunk: usize,
    left_of_chunk: u32,
}

impl<const N: usize, const NBITS: u32> Iterator
    for BitArrayNBitsIter<N, NBITS>
{
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.left_of_chunk == 0 {
            self.chunk_ind += 1;
            self.cur_chunk = *self.data.get(self.chunk_ind)?;
            self.left_of_chunk = usize::BITS / NBITS;
        }

        let mask = (!0) >> (usize::BITS - NBITS);

        self.left_of_chunk -= 1;
        let val = self.cur_chunk & mask;
        self.cur_chunk >>= NBITS;

        Some(val)
    }
}
