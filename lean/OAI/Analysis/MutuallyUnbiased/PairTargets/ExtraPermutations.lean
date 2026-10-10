import OAI.Analysis.MutuallyUnbiased.Certificate.Canonical

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def extraPermutation0 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation1 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation2 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation3 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation4 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation5 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation6 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation7 : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation8 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation9 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation11 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation12 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation13 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation14 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation15 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation16 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation17 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation18 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation19 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation20 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation21 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation22 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation23 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation24 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation25 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation26 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation27 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation28 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation29 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation30 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation31 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation32 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation33 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation34 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation35 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 4, 3]
  invFun := ![1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation36 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation37 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation38 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 0, 2]
  invFun := ![3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation39 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation40 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation41 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 1, 3]
  invFun := ![2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation42 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation43 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation44 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 1, 0]
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation45 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation46 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 0, 2]
  invFun := ![3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation47 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 2, 0]
  invFun := ![4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation48 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation49 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation50 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 1, 3]
  invFun := ![2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation51 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 1, 0]
  invFun := ![4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation52 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 1, 2]
  invFun := ![2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation53 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 0, 2]
  invFun := ![3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation54 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 2, 0]
  invFun := ![4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation55 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 1, 0]
  invFun := ![4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation56 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation57 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation58 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation59 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation60 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation61 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation62 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation63 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation64 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation65 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation66 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extraPermutation67 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
