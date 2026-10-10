import OAI.Analysis.MutuallyUnbiased.Certificate.Canonical

namespace OAI

namespace MUB6.Certificate.PairSemantics

def permutation0 : Equiv.Perm (Fin 1) where
  toFun := ![0]
  invFun := ![0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation1 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation2 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation3 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation4 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation5 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation6 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation7 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation8 : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation9 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation11 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation12 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation13 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation14 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 2, 1]
  invFun := ![0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation15 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation16 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation17 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation18 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation19 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation20 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation21 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation22 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation23 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation24 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation25 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation26 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation27 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation28 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 2, 1]
  invFun := ![1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation29 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation30 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation31 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation32 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation33 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation34 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation35 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation36 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation37 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation38 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 3, 2]
  invFun := ![0, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation39 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation40 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation41 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation42 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation43 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation44 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 3, 1]
  invFun := ![0, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation45 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 1, 2, 4]
  invFun := ![0, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation46 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 1, 4, 2]
  invFun := ![0, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation47 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 2, 1, 4]
  invFun := ![0, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation48 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 2, 4, 1]
  invFun := ![0, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation49 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation50 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 2, 1]
  invFun := ![0, 4, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation51 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 1, 2, 3]
  invFun := ![0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation52 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 1, 3, 2]
  invFun := ![0, 2, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation53 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 2, 1, 3]
  invFun := ![0, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation54 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 2, 3, 1]
  invFun := ![0, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation55 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 3, 1, 2]
  invFun := ![0, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation56 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 3, 2, 1]
  invFun := ![0, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation57 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation58 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 4, 3]
  invFun := ![1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation59 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 2, 4]
  invFun := ![1, 0, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation60 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation61 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 4, 2, 3]
  invFun := ![1, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation62 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 4, 3, 2]
  invFun := ![1, 0, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation63 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation64 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 0, 4]
  invFun := ![3, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation65 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation66 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 4, 0, 3]
  invFun := ![3, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation67 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 4, 3, 0]
  invFun := ![4, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation68 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 0, 2, 4]
  invFun := ![2, 0, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation69 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 0, 4, 2]
  invFun := ![2, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation70 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 2, 0, 4]
  invFun := ![3, 0, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation71 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 2, 4, 0]
  invFun := ![4, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation72 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 0, 2]
  invFun := ![3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation73 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 2, 0]
  invFun := ![4, 0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation74 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 0, 2, 3]
  invFun := ![2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation75 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 0, 3, 2]
  invFun := ![2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation76 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 2, 0, 3]
  invFun := ![3, 0, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation77 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 2, 3, 0]
  invFun := ![4, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation78 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 3, 0, 2]
  invFun := ![3, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation79 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 3, 2, 0]
  invFun := ![4, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation80 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation81 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 4, 3]
  invFun := ![1, 2, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation82 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 1, 4]
  invFun := ![1, 3, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation83 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 4, 1]
  invFun := ![1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation84 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 1, 3]
  invFun := ![1, 3, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation85 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 3, 1]
  invFun := ![1, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation86 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 0, 3, 4]
  invFun := ![2, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation87 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 0, 4, 3]
  invFun := ![2, 1, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation88 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 3, 0, 4]
  invFun := ![3, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation89 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 3, 4, 0]
  invFun := ![4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation90 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 4, 0, 3]
  invFun := ![3, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation91 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 4, 3, 0]
  invFun := ![4, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation92 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation93 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 4, 1]
  invFun := ![2, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation94 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 1, 0, 4]
  invFun := ![3, 2, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation95 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 1, 4, 0]
  invFun := ![4, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation96 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 0, 1]
  invFun := ![3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation97 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 1, 0]
  invFun := ![4, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation98 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 1, 3]
  invFun := ![2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation99 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 3, 1]
  invFun := ![2, 4, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation100 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 1, 0, 3]
  invFun := ![3, 2, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation101 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 1, 3, 0]
  invFun := ![4, 2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation102 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 0, 1]
  invFun := ![3, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation103 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 1, 0]
  invFun := ![4, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation104 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation105 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 4, 2]
  invFun := ![1, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation106 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 2, 1, 4]
  invFun := ![1, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation107 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 2, 4, 1]
  invFun := ![1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation108 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 1, 2]
  invFun := ![1, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation109 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 2, 1]
  invFun := ![1, 4, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation110 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 0, 2, 4]
  invFun := ![2, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation111 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 0, 4, 2]
  invFun := ![2, 1, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation112 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 2, 0, 4]
  invFun := ![3, 1, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation113 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 2, 4, 0]
  invFun := ![4, 1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation114 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 4, 0, 2]
  invFun := ![3, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation115 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 4, 2, 0]
  invFun := ![4, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation116 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation117 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 4, 1]
  invFun := ![2, 4, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation118 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 1, 0, 4]
  invFun := ![3, 2, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation119 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 1, 4, 0]
  invFun := ![4, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation120 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 0, 1]
  invFun := ![3, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation121 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 1, 0]
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation122 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation123 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 2, 1]
  invFun := ![2, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation124 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 0, 2]
  invFun := ![3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation125 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 2, 0]
  invFun := ![4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation126 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 0, 1]
  invFun := ![3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation127 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation128 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation129 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 3, 2]
  invFun := ![1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation130 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 2, 1, 3]
  invFun := ![1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation131 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 2, 3, 1]
  invFun := ![1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation132 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 3, 1, 2]
  invFun := ![1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation133 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 0, 2, 3]
  invFun := ![2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation134 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 0, 3, 2]
  invFun := ![2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation135 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 2, 0, 3]
  invFun := ![3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation136 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 2, 3, 0]
  invFun := ![4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation137 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 3, 0, 2]
  invFun := ![3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation138 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 3, 2, 0]
  invFun := ![4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation139 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 1, 3]
  invFun := ![2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation140 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 3, 1]
  invFun := ![2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation141 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 1, 0, 3]
  invFun := ![3, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation142 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 1, 3, 0]
  invFun := ![4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation143 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 0, 1]
  invFun := ![3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation144 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 1, 0]
  invFun := ![4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation145 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 1, 2]
  invFun := ![2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation146 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 2, 1]
  invFun := ![2, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation147 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 0, 2]
  invFun := ![3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation148 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 2, 0]
  invFun := ![4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation149 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 0, 1]
  invFun := ![3, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation150 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 1, 0]
  invFun := ![4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation151 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation152 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation153 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation154 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation155 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation156 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 4, 5]
  invFun := ![0, 1, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation157 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 5, 4]
  invFun := ![0, 1, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation158 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 2, 5]
  invFun := ![0, 1, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation159 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 5, 2]
  invFun := ![0, 1, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation160 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 5, 2, 4]
  invFun := ![0, 1, 4, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation161 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 5, 4, 2]
  invFun := ![0, 1, 5, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation162 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation163 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 3, 5, 2]
  invFun := ![0, 1, 5, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation164 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation165 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation166 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation167 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation168 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 5, 3, 4]
  invFun := ![0, 2, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation169 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 4, 5]
  invFun := ![0, 3, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation170 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 5, 4]
  invFun := ![0, 3, 1, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation171 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 1, 5]
  invFun := ![0, 4, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation172 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation173 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 5, 3]
  invFun := ![0, 3, 1, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation174 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 5, 1, 3]
  invFun := ![0, 4, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation175 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 1, 3, 4]
  invFun := ![0, 3, 1, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation176 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation177 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation178 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation179 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 2, 1, 5]
  invFun := ![0, 4, 3, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation180 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation181 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation182 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 5, 3]
  invFun := ![0, 2, 3, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation183 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 3, 2, 5]
  invFun := ![0, 2, 4, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation184 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 3, 5, 2]
  invFun := ![0, 2, 5, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation185 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation186 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 3, 2]
  invFun := ![0, 2, 5, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation187 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 1, 5, 3]
  invFun := ![0, 3, 2, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation188 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 3, 1, 5]
  invFun := ![0, 4, 2, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation189 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 3, 5, 1]
  invFun := ![0, 5, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation190 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 5, 1, 3]
  invFun := ![0, 4, 2, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation191 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 5, 3, 1]
  invFun := ![0, 5, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation192 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 1, 2, 5]
  invFun := ![0, 3, 4, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation193 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 2, 5, 1]
  invFun := ![0, 5, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation194 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 5, 1, 2]
  invFun := ![0, 4, 5, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation195 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation196 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation197 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation198 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 4, 2, 3]
  invFun := ![0, 2, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation199 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 3, 4, 1]
  invFun := ![0, 5, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation200 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation201 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation202 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation203 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 5, 3, 4]
  invFun := ![1, 0, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation204 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 4, 2, 5]
  invFun := ![1, 0, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation205 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 4, 5, 2]
  invFun := ![1, 0, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation206 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 5, 2, 3]
  invFun := ![1, 0, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation207 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 5, 3, 4]
  invFun := ![2, 0, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation208 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 5, 4, 0]
  invFun := ![5, 0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation209 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 5, 0, 3]
  invFun := ![4, 0, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation210 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 5, 3, 0]
  invFun := ![5, 0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation211 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 5, 4, 3, 0]
  invFun := ![5, 0, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation212 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 5, 4, 2]
  invFun := ![2, 0, 5, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation213 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 5, 0, 2]
  invFun := ![4, 0, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation214 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 5, 2, 3]
  invFun := ![2, 0, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation215 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 3, 4]
  invFun := ![2, 0, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation216 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 4, 3]
  invFun := ![2, 0, 3, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation217 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 4, 2, 3]
  invFun := ![2, 0, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation218 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 4, 3, 2]
  invFun := ![2, 0, 5, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation219 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 2, 3, 4, 0]
  invFun := ![5, 0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation220 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 3, 2, 4, 0]
  invFun := ![5, 0, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation221 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation222 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation223 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation224 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation225 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 1, 4, 5]
  invFun := ![1, 3, 0, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation226 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 4, 5, 1]
  invFun := ![1, 5, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation227 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 3, 4, 5, 0]
  invFun := ![5, 1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation228 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation229 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation230 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 5, 1]
  invFun := ![3, 5, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation231 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation232 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 1, 0]
  invFun := ![5, 4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation233 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation234 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 3, 5, 0, 1]
  invFun := ![4, 5, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation235 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation236 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation237 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 3, 4, 0]
  invFun := ![5, 2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation238 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 4, 3, 0]
  invFun := ![5, 2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation239 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 3, 0, 1, 4]
  invFun := ![3, 4, 0, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation240 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation241 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation242 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation243 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 1, 4, 5]
  invFun := ![1, 3, 2, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation244 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 4, 1, 5]
  invFun := ![1, 4, 2, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation245 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 5, 1, 2]
  invFun := ![1, 4, 5, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation246 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 2, 4, 0, 5]
  invFun := ![4, 1, 2, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation247 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 0, 1, 5]
  invFun := ![3, 4, 1, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation248 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation249 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation250 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 0, 5, 2]
  invFun := ![3, 2, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation251 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation252 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation253 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation254 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation255 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation256 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation257 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation258 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation259 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation260 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 2, 5]
  invFun := ![1, 2, 4, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation261 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 5, 2]
  invFun := ![1, 2, 5, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation262 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation263 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 3, 2]
  invFun := ![1, 2, 5, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation264 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 1, 3, 5]
  invFun := ![1, 3, 2, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation265 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 1, 5, 3]
  invFun := ![1, 3, 2, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation266 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 3, 1, 5]
  invFun := ![1, 4, 2, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation267 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 3, 5, 1]
  invFun := ![1, 5, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation268 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 5, 1, 3]
  invFun := ![1, 4, 2, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation269 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 2, 5, 3, 1]
  invFun := ![1, 5, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation270 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 1, 2, 5]
  invFun := ![1, 3, 4, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation271 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 1, 5, 2]
  invFun := ![1, 3, 5, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation272 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 2, 1, 5]
  invFun := ![1, 4, 3, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation273 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 2, 5, 1]
  invFun := ![1, 5, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation274 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 5, 1, 2]
  invFun := ![1, 4, 5, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation275 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation276 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation277 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 2, 3, 5]
  invFun := ![2, 1, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation278 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 2, 5, 3]
  invFun := ![2, 1, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation279 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 5, 2, 3]
  invFun := ![2, 1, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation280 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 0, 3, 5]
  invFun := ![3, 1, 2, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation281 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 3, 2, 0, 5]
  invFun := ![4, 1, 3, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation282 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 3, 5, 2, 0]
  invFun := ![5, 1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation283 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 1, 3, 5]
  invFun := ![2, 3, 1, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation284 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 1, 5, 3]
  invFun := ![2, 3, 1, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation285 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 3, 5, 1]
  invFun := ![2, 5, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation286 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation287 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation288 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation289 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation290 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation291 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 2, 5, 0]
  invFun := ![5, 2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation292 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation293 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation294 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation295 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation296 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 2, 1, 3]
  invFun := ![2, 4, 3, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation297 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation298 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation299 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation300 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation301 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 1, 3, 0]
  invFun := ![5, 3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation302 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation303 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation304 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation305 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation306 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 1, 2, 0]
  invFun := ![5, 3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation307 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation308 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation309 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 4, 3]
  invFun := ![1, 2, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation310 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 3, 2, 4]
  invFun := ![1, 2, 4, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation311 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 3, 4, 2]
  invFun := ![1, 2, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation312 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 2, 3]
  invFun := ![1, 2, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation313 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 3, 2]
  invFun := ![1, 2, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation314 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 1, 3, 4]
  invFun := ![1, 3, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation315 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 1, 4, 3]
  invFun := ![1, 3, 2, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation316 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 3, 1, 4]
  invFun := ![1, 4, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation317 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 3, 4, 1]
  invFun := ![1, 5, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation318 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 4, 1, 3]
  invFun := ![1, 4, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation319 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 4, 3, 1]
  invFun := ![1, 5, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation320 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 1, 2, 4]
  invFun := ![1, 3, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation321 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 1, 4, 2]
  invFun := ![1, 3, 5, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation322 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 2, 1, 4]
  invFun := ![1, 4, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation323 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 2, 4, 1]
  invFun := ![1, 5, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation324 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 4, 1, 2]
  invFun := ![1, 4, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation325 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 4, 2, 1]
  invFun := ![1, 5, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation326 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation327 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation328 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 2, 3, 1]
  invFun := ![1, 5, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation329 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 3, 1, 2]
  invFun := ![1, 4, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation330 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 3, 2, 1]
  invFun := ![1, 5, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation331 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 2, 3, 4]
  invFun := ![2, 1, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation332 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 2, 4, 3]
  invFun := ![2, 1, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation333 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 3, 2, 4]
  invFun := ![2, 1, 4, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation334 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 3, 4, 2]
  invFun := ![2, 1, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation335 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 4, 2, 3]
  invFun := ![2, 1, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation336 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 4, 3, 2]
  invFun := ![2, 1, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation337 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 0, 3, 4]
  invFun := ![3, 1, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation338 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 0, 4, 3]
  invFun := ![3, 1, 2, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation339 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 3, 0, 4]
  invFun := ![4, 1, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation340 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 3, 4, 0]
  invFun := ![5, 1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation341 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 4, 0, 3]
  invFun := ![4, 1, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation342 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 4, 3, 0]
  invFun := ![5, 1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation343 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 0, 2, 4]
  invFun := ![3, 1, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation344 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 0, 4, 2]
  invFun := ![3, 1, 5, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation345 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 2, 0, 4]
  invFun := ![4, 1, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation346 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 2, 4, 0]
  invFun := ![5, 1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation347 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 4, 0, 2]
  invFun := ![4, 1, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation348 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 4, 2, 0]
  invFun := ![5, 1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation349 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 0, 2, 3]
  invFun := ![3, 1, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation350 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 0, 3, 2]
  invFun := ![3, 1, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation351 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 2, 0, 3]
  invFun := ![4, 1, 3, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation352 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 2, 3, 0]
  invFun := ![5, 1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation353 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 3, 0, 2]
  invFun := ![4, 1, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation354 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 3, 2, 0]
  invFun := ![5, 1, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation355 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation356 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 4, 3]
  invFun := ![2, 3, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation357 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 0, 3, 4]
  invFun := ![3, 2, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation358 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 0, 4, 3]
  invFun := ![3, 2, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation359 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 3, 0, 4]
  invFun := ![4, 2, 1, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation360 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 3, 4, 0]
  invFun := ![5, 2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation361 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 0, 3]
  invFun := ![4, 2, 1, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation362 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 3, 0]
  invFun := ![5, 2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation363 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 0, 1, 4]
  invFun := ![3, 4, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation364 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 1, 0, 4]
  invFun := ![4, 3, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation365 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 1, 4, 0]
  invFun := ![5, 3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation366 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 4, 0, 1]
  invFun := ![4, 5, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation367 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 4, 1, 0]
  invFun := ![5, 4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation368 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation369 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation370 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 1, 3, 0]
  invFun := ![5, 3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation371 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 3, 0, 1]
  invFun := ![4, 5, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation372 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 3, 1, 0]
  invFun := ![5, 4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation373 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation374 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 4, 2]
  invFun := ![2, 3, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation375 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 2, 1, 4]
  invFun := ![2, 4, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation376 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 4, 2, 1]
  invFun := ![2, 5, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation377 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 0, 2, 4]
  invFun := ![3, 2, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation378 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 0, 4, 2]
  invFun := ![3, 2, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation379 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation380 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation381 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 4, 0, 2]
  invFun := ![4, 2, 5, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation382 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 4, 2, 0]
  invFun := ![5, 2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation383 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 0, 1, 4]
  invFun := ![3, 4, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation384 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 0, 4, 1]
  invFun := ![3, 5, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation385 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 1, 0, 4]
  invFun := ![4, 3, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation386 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 1, 4, 0]
  invFun := ![5, 3, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation387 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 4, 0, 1]
  invFun := ![4, 5, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation388 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 4, 1, 0]
  invFun := ![5, 4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation389 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation390 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation391 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation392 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 1, 2, 0]
  invFun := ![5, 3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation393 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation394 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 2, 1, 0]
  invFun := ![5, 4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation395 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation396 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation397 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation398 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation399 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation400 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation401 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation402 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation403 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 1, 0, 3]
  invFun := ![4, 3, 2, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation404 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation405 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation406 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation407 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation408 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation409 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end MUB6.Certificate.PairSemantics

end OAI
