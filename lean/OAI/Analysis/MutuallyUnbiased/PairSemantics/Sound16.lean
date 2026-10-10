import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical248
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical265

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1024 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -3, 1, 2], ![2, 3, -2, -3]]

theorem sound1024 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1024 = Sparse.eval value1024 (momentVector H) := by
  have heq : pivotMatrix1024 = (fun u v => node1024.transpose (pivotPermutation1024 u) v) := by apply Matrix.ext; unfold pivotMatrix1024 node1024 pivotPermutation1024; decide +kernel
  have hmoment : injectiveMoment H node1024 = injectiveMoment H pivotMatrix1024 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1024 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1024 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1024 (0 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1024 (0 : Fin 3) = raw3655 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1024 raw3655; decide +kernel
    rw [heq]
    exact (canonical3655 hH).trans (sound196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1024 (1 : Fin 3)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1024 (1 : Fin 3) = raw7471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1024 raw7471; decide +kernel
    rw [heq]
    exact (canonical7471 hH).trans (sound277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1024 (2 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1024 (2 : Fin 3) = raw7481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1024 raw7481; decide +kernel
    rw [heq]
    exact (canonical7481 hH).trans (sound280 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1024 + (injectiveMoment H (mergeFirst pivotMatrix1024 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1024 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1024 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1024, value196, value277, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1025 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -3, 0, 3], ![2, 3, -2, -3]]

theorem sound1025 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1025 = Sparse.eval value1025 (momentVector H) := by
  have heq : pivotMatrix1025 = (fun u v => node1025.transpose (pivotPermutation1025 u) v) := by apply Matrix.ext; unfold pivotMatrix1025 node1025 pivotPermutation1025; decide +kernel
  have hmoment : injectiveMoment H node1025 = injectiveMoment H pivotMatrix1025 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1025 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1025 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1025 (0 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1025 (0 : Fin 3) = raw4177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1025 raw4177; decide +kernel
    rw [heq]
    exact (canonical4177 hH).trans (sound192 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1025 (1 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1025 (1 : Fin 3) = raw7527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1025 raw7527; decide +kernel
    rw [heq]
    exact (canonical7527 hH).trans (sound213 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1025 (2 : Fin 3)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1025 (2 : Fin 3) = raw7546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1025 raw7546; decide +kernel
    rw [heq]
    exact (canonical7546 hH).trans (sound214 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1025 + (injectiveMoment H (mergeFirst pivotMatrix1025 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1025 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1025 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1025, value192, value213, value214, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1026 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -3, 2, 1], ![2, 3, -4, -1]]

theorem sound1026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1026 = Sparse.eval value1026 (momentVector H) := by
  have heq : pivotMatrix1026 = (fun u v => node1026.transpose (pivotPermutation1026 u) v) := by apply Matrix.ext; unfold pivotMatrix1026 node1026 pivotPermutation1026; decide +kernel
  have hmoment : injectiveMoment H node1026 = injectiveMoment H pivotMatrix1026 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1026 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1026 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1026 (0 : Fin 3)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1026 (0 : Fin 3) = raw4178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1026 raw4178; decide +kernel
    rw [heq]
    exact (canonical4178 hH).trans (sound141 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1026 (1 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1026 (1 : Fin 3) = raw7528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1026 raw7528; decide +kernel
    rw [heq]
    exact (canonical7528 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1026 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1026 (2 : Fin 3) = raw7548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1026 raw7548; decide +kernel
    rw [heq]
    exact (canonical7548 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1026 + (injectiveMoment H (mergeFirst pivotMatrix1026 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1026 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1026 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1026, value141, value154, value155, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1027 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, 2, -2, -2]]

theorem sound1027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1027 = Sparse.eval value1027 (momentVector H) := by
  have heq : pivotMatrix1027 = (fun u v => node1027.transpose (pivotPermutation1027 u) v) := by apply Matrix.ext; unfold pivotMatrix1027 node1027 pivotPermutation1027; decide +kernel
  have hmoment : injectiveMoment H node1027 = injectiveMoment H pivotMatrix1027 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1027 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1027 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (0 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (1 : Fin 3) = raw7257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7257; decide +kernel
    rw [heq]
    exact (canonical7257 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (2 : Fin 3) = raw7281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7281; decide +kernel
    rw [heq]
    exact (canonical7281 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1027 + (injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1027, value197, value279, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1028 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -2, 3, -1], ![2, 2, -3, -1]]

theorem sound1028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1028 = Sparse.eval value1028 (momentVector H) := by
  have heq : pivotMatrix1028 = (fun u v => node1028.transpose (pivotPermutation1028 u) v) := by apply Matrix.ext; unfold pivotMatrix1028 node1028 pivotPermutation1028; decide +kernel
  have hmoment : injectiveMoment H node1028 = injectiveMoment H pivotMatrix1028 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1028 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1028 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1028 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1028 (0 : Fin 3) = raw3350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1028 raw3350; decide +kernel
    rw [heq]
    exact (canonical3350 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1028 (1 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1028 (1 : Fin 3) = raw7258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1028 raw7258; decide +kernel
    rw [heq]
    exact (canonical7258 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1028 (2 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1028 (2 : Fin 3) = raw7282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1028 raw7282; decide +kernel
    rw [heq]
    exact (canonical7282 hH).trans (sound292 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1028 + (injectiveMoment H (mergeFirst pivotMatrix1028 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1028 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1028 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1028, value198, value280, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1029 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -2, 4, -2], ![2, 2, -4, 0]]

theorem sound1029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1029 = Sparse.eval value1029 (momentVector H) := by
  have heq : pivotMatrix1029 = (fun u v => node1029.transpose (pivotPermutation1029 u) v) := by apply Matrix.ext; unfold pivotMatrix1029 node1029 pivotPermutation1029; decide +kernel
  have hmoment : injectiveMoment H node1029 = injectiveMoment H pivotMatrix1029 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1029 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1029 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1029 (0 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1029 (0 : Fin 3) = raw3351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1029 raw3351; decide +kernel
    rw [heq]
    exact (canonical3351 hH).trans (sound199 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1029 (1 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1029 (1 : Fin 3) = raw7259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1029 raw7259; decide +kernel
    rw [heq]
    exact (canonical7259 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1029 (2 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1029 (2 : Fin 3) = raw7283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1029 raw7283; decide +kernel
    rw [heq]
    exact (canonical7283 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1029 + (injectiveMoment H (mergeFirst pivotMatrix1029 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1029 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1029 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1029, value199, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1030 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1030 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -2, -2, 4], ![2, 2, 1, -5]]

theorem sound1030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1030 = Sparse.eval value1030 (momentVector H) := by
  have heq : pivotMatrix1030 = (fun u v => node1030.transpose (pivotPermutation1030 u) v) := by apply Matrix.ext; unfold pivotMatrix1030 node1030 pivotPermutation1030; decide +kernel
  have hmoment : injectiveMoment H node1030 = injectiveMoment H pivotMatrix1030 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1030 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1030 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1030 (0 : Fin 3)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1030 (0 : Fin 3) = raw3656 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1030 raw3656; decide +kernel
    rw [heq]
    exact (canonical3656 hH).trans (sound200 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1030 (1 : Fin 3)) =
      Sparse.eval value282 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1030 (1 : Fin 3) = raw7472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1030 raw7472; decide +kernel
    rw [heq]
    exact (canonical7472 hH).trans (sound282 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1030 (2 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1030 (2 : Fin 3) = raw7482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1030 raw7482; decide +kernel
    rw [heq]
    exact (canonical7482 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1030 + (injectiveMoment H (mergeFirst pivotMatrix1030 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1030 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1030 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1030, value200, value281, value282, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1031 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1031 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![1, 0, 3, -4]]

theorem sound1031 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1031 = Sparse.eval value1031 (momentVector H) := by
  have heq : pivotMatrix1031 = (fun u v => node1031 (pivotPermutation1031 u) v) := by apply Matrix.ext; unfold pivotMatrix1031 node1031 pivotPermutation1031; decide +kernel
  have hmoment : injectiveMoment H node1031 = injectiveMoment H pivotMatrix1031 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1031 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1031 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1031 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1031 (0 : Fin 3) = raw7191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1031 raw7191; decide +kernel
    rw [heq]
    exact (canonical7191 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1031 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1031 (1 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1031 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1031 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1031 (2 : Fin 3) = raw6437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1031 raw6437; decide +kernel
    rw [heq]
    exact (canonical6437 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1031 + (injectiveMoment H (mergeFirst pivotMatrix1031 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1031 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1031 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1031, value145, value155, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1032 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1032 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![1, 0, 2, -3]]

theorem sound1032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1032 = Sparse.eval value1032 (momentVector H) := by
  have heq : pivotMatrix1032 = (fun u v => node1032 (pivotPermutation1032 u) v) := by apply Matrix.ext; unfold pivotMatrix1032 node1032 pivotPermutation1032; decide +kernel
  have hmoment : injectiveMoment H node1032 = injectiveMoment H pivotMatrix1032 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1032 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1032 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1032 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1032 (0 : Fin 3) = raw7333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1032 raw7333; decide +kernel
    rw [heq]
    exact (canonical7333 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1032 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1032 (1 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1032 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1032 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1032 (2 : Fin 3) = raw6437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1032 raw6437; decide +kernel
    rw [heq]
    exact (canonical6437 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1032 + (injectiveMoment H (mergeFirst pivotMatrix1032 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1032 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1032 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1032, value145, value185, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1033 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -2, 1, 1], ![2, 2, -2, -2]]

theorem sound1033 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1033 = Sparse.eval value1033 (momentVector H) := by
  have heq : pivotMatrix1033 = (fun u v => node1033.transpose (pivotPermutation1033 u) v) := by apply Matrix.ext; unfold pivotMatrix1033 node1033 pivotPermutation1033; decide +kernel
  have hmoment : injectiveMoment H node1033 = injectiveMoment H pivotMatrix1033 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1033 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1033 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1033 (0 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1033 (0 : Fin 3) = raw3674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1033 raw3674; decide +kernel
    rw [heq]
    exact (canonical3674 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1033 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1033 (1 : Fin 3) = raw7473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1033 raw7473; decide +kernel
    rw [heq]
    exact (canonical7473 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1033 (2 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1033 (2 : Fin 3) = raw7483 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1033 raw7483; decide +kernel
    rw [heq]
    exact (canonical7483 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1033 + (injectiveMoment H (mergeFirst pivotMatrix1033 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1033 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1033 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1033, value202, value279, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1034 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, -2, 4], ![2, 2, 0, -4]]

theorem sound1034 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1034 = Sparse.eval value1034 (momentVector H) := by
  have heq : pivotMatrix1034 = (fun u v => node1034.transpose (pivotPermutation1034 u) v) := by apply Matrix.ext; unfold pivotMatrix1034 node1034 pivotPermutation1034; decide +kernel
  have hmoment : injectiveMoment H node1034 = injectiveMoment H pivotMatrix1034 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1034 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1034 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1034 (0 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1034 (0 : Fin 3) = raw4179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1034 raw4179; decide +kernel
    rw [heq]
    exact (canonical4179 hH).trans (sound199 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1034 (1 : Fin 3)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1034 (1 : Fin 3) = raw7529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1034 raw7529; decide +kernel
    rw [heq]
    exact (canonical7529 hH).trans (sound200 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1034 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1034 (2 : Fin 3) = raw7549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1034 raw7549; decide +kernel
    rw [heq]
    exact (canonical7549 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1034 + (injectiveMoment H (mergeFirst pivotMatrix1034 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1034 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1034 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1034, value199, value200, value201, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1035 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, -1, 3], ![2, 2, -1, -3]]

theorem sound1035 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1035 = Sparse.eval value1035 (momentVector H) := by
  have heq : pivotMatrix1035 = (fun u v => node1035.transpose (pivotPermutation1035 u) v) := by apply Matrix.ext; unfold pivotMatrix1035 node1035 pivotPermutation1035; decide +kernel
  have hmoment : injectiveMoment H node1035 = injectiveMoment H pivotMatrix1035 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1035 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1035 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1035 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1035 (0 : Fin 3) = raw4180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1035 raw4180; decide +kernel
    rw [heq]
    exact (canonical4180 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1035 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1035 (1 : Fin 3) = raw7530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1035 raw7530; decide +kernel
    rw [heq]
    exact (canonical7530 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1035 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1035 (2 : Fin 3) = raw7550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1035 raw7550; decide +kernel
    rw [heq]
    exact (canonical7550 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1035 + (injectiveMoment H (mergeFirst pivotMatrix1035 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1035 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1035 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1035, value198, value225, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1036 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, 1, 1], ![2, 2, -3, -1]]

theorem sound1036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1036 = Sparse.eval value1036 (momentVector H) := by
  have heq : pivotMatrix1036 = (fun u v => node1036.transpose (pivotPermutation1036 u) v) := by apply Matrix.ext; unfold pivotMatrix1036 node1036 pivotPermutation1036; decide +kernel
  have hmoment : injectiveMoment H node1036 = injectiveMoment H pivotMatrix1036 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1036 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1036 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1036 (0 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1036 (0 : Fin 3) = raw4182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1036 raw4182; decide +kernel
    rw [heq]
    exact (canonical4182 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1036 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1036 (1 : Fin 3) = raw7532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1036 raw7532; decide +kernel
    rw [heq]
    exact (canonical7532 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1036 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1036 (2 : Fin 3) = raw7555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1036 raw7555; decide +kernel
    rw [heq]
    exact (canonical7555 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1036 + (injectiveMoment H (mergeFirst pivotMatrix1036 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1036 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1036 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1036, value169, value184, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1037 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1037 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

theorem sound1037 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1037 = Sparse.eval value1037 (momentVector H) := by
  have heq : pivotMatrix1037 = (fun u v => node1037 (pivotPermutation1037 u) v) := by apply Matrix.ext; unfold pivotMatrix1037 node1037 pivotPermutation1037; decide +kernel
  have hmoment : injectiveMoment H node1037 = injectiveMoment H pivotMatrix1037 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1037 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1037 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1037 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1037 (0 : Fin 3) = raw8069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1037 raw8069; decide +kernel
    rw [heq]
    exact (canonical8069 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1037 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1037 (1 : Fin 3) = raw6561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1037 raw6561; decide +kernel
    rw [heq]
    exact (canonical6561 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1037 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1037 (2 : Fin 3) = raw6437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1037 raw6437; decide +kernel
    rw [heq]
    exact (canonical6437 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1037 + (injectiveMoment H (mergeFirst pivotMatrix1037 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1037 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1037 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1037, value145, value153, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1038 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, -2, 3, -1], ![2, 2, -5, 1]]

theorem sound1038 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1038 = Sparse.eval value1038 (momentVector H) := by
  have heq : pivotMatrix1038 = (fun u v => node1038.transpose (pivotPermutation1038 u) v) := by apply Matrix.ext; unfold pivotMatrix1038 node1038 pivotPermutation1038; decide +kernel
  have hmoment : injectiveMoment H node1038 = injectiveMoment H pivotMatrix1038 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1038 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1038 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1038 (0 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1038 (0 : Fin 3) = raw4183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1038 raw4183; decide +kernel
    rw [heq]
    exact (canonical4183 hH).trans (sound120 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1038 (1 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1038 (1 : Fin 3) = raw7534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1038 raw7534; decide +kernel
    rw [heq]
    exact (canonical7534 hH).trans (sound127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1038 (2 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1038 (2 : Fin 3) = raw7557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1038 raw7557; decide +kernel
    rw [heq]
    exact (canonical7557 hH).trans (sound127 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1038 + (injectiveMoment H (mergeFirst pivotMatrix1038 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1038 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1038 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1038, value120, value127, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1039 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1039 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem sound1039 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1039 = Sparse.eval value1039 (momentVector H) := by
  have heq : pivotMatrix1039 = (fun u v => node1039 (pivotPermutation1039 u) v) := by apply Matrix.ext; unfold pivotMatrix1039 node1039 pivotPermutation1039; decide +kernel
  have hmoment : injectiveMoment H node1039 = injectiveMoment H pivotMatrix1039 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1039 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1039 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1039 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1039 (0 : Fin 3) = raw6283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1039 raw6283; decide +kernel
    rw [heq]
    exact (canonical6283 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1039 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1039 (1 : Fin 3) = raw6475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1039 raw6475; decide +kernel
    rw [heq]
    exact (canonical6475 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1039 (2 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1039 (2 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1039 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1039 + (injectiveMoment H (mergeFirst pivotMatrix1039 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1039 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1039 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1039, value11, value271, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1040 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1040 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem sound1040 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1040 = Sparse.eval value1040 (momentVector H) := by
  have heq : pivotMatrix1040 = (fun u v => node1040 (pivotPermutation1040 u) v) := by apply Matrix.ext; unfold pivotMatrix1040 node1040 pivotPermutation1040; decide +kernel
  have hmoment : injectiveMoment H node1040 = injectiveMoment H pivotMatrix1040 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1040 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1040 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1040 (0 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1040 (0 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1040 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1040 (1 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1040 (1 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1040 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1040 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1040 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1040 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1040 + (injectiveMoment H (mergeFirst pivotMatrix1040 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1040 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1040 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1040, value176, value207, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1041 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1041 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem sound1041 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1041 = Sparse.eval value1041 (momentVector H) := by
  have heq : pivotMatrix1041 = (fun u v => node1041 (pivotPermutation1041 u) v) := by apply Matrix.ext; unfold pivotMatrix1041 node1041 pivotPermutation1041; decide +kernel
  have hmoment : injectiveMoment H node1041 = injectiveMoment H pivotMatrix1041 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1041 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1041 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1041 (0 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1041 (0 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1041 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1041 (1 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1041 (1 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1041 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1041 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1041 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1041 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1041 + (injectiveMoment H (mergeFirst pivotMatrix1041 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1041 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1041 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1041, value188, value207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1042 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1042 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem sound1042 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1042 = Sparse.eval value1042 (momentVector H) := by
  have heq : pivotMatrix1042 = (fun u v => node1042 (pivotPermutation1042 u) v) := by apply Matrix.ext; unfold pivotMatrix1042 node1042 pivotPermutation1042; decide +kernel
  have hmoment : injectiveMoment H node1042 = injectiveMoment H pivotMatrix1042 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1042 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1042 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1042 (0 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1042 (0 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1042 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1042 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1042 (1 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1042 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1042 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1042 (2 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1042 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1042 + (injectiveMoment H (mergeFirst pivotMatrix1042 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1042 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1042 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1042, value155, value173, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1043 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1043 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem sound1043 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1043 = Sparse.eval value1043 (momentVector H) := by
  have heq : pivotMatrix1043 = (fun u v => node1043 (pivotPermutation1043 u) v) := by apply Matrix.ext; unfold pivotMatrix1043 node1043 pivotPermutation1043; decide +kernel
  have hmoment : injectiveMoment H node1043 = injectiveMoment H pivotMatrix1043 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1043 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1043 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1043 (0 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1043 (0 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1043 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1043 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1043 (1 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1043 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1043 (2 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1043 (2 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1043 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1043 + (injectiveMoment H (mergeFirst pivotMatrix1043 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1043 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1043 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1043, value185, value285, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1044 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1044 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound1044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1044 = Sparse.eval value1044 (momentVector H) := by
  have heq : pivotMatrix1044 = (fun u v => node1044 (pivotPermutation1044 u) v) := by apply Matrix.ext; unfold pivotMatrix1044 node1044 pivotPermutation1044; decide +kernel
  have hmoment : injectiveMoment H node1044 = injectiveMoment H pivotMatrix1044 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1044 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1044 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1044 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1044 (0 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1044 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1044 (1 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1044 (1 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1044 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1044 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1044 (2 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1044 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1044 + (injectiveMoment H (mergeFirst pivotMatrix1044 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1044 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1044 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1044, value271, value294, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1045 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1045 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![1, 1, -2, 0]]

theorem sound1045 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1045 = Sparse.eval value1045 (momentVector H) := by
  have heq : pivotMatrix1045 = (fun u v => node1045 (pivotPermutation1045 u) v) := by apply Matrix.ext; unfold pivotMatrix1045 node1045 pivotPermutation1045; decide +kernel
  have hmoment : injectiveMoment H node1045 = injectiveMoment H pivotMatrix1045 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1045 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1045 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1045 (0 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1045 (0 : Fin 3) = raw6680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1045 raw6680; decide +kernel
    rw [heq]
    exact (canonical6680 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1045 (1 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1045 (1 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1045 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1045 (2 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1045 (2 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1045 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1045 + (injectiveMoment H (mergeFirst pivotMatrix1045 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1045 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1045 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1045, value207, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1046 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1046 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -3, 2], ![1, 0, 2, -3]]

theorem sound1046 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1046 = Sparse.eval value1046 (momentVector H) := by
  have heq : pivotMatrix1046 = (fun u v => node1046 (pivotPermutation1046 u) v) := by apply Matrix.ext; unfold pivotMatrix1046 node1046 pivotPermutation1046; decide +kernel
  have hmoment : injectiveMoment H node1046 = injectiveMoment H pivotMatrix1046 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1046 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1046 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1046 (0 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1046 (0 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1046 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1046 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1046 (1 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1046 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1046 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1046 (2 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1046 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1046 + (injectiveMoment H (mergeFirst pivotMatrix1046 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1046 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1046 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1046, value155, value185, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1047 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1047 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem sound1047 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1047 = Sparse.eval value1047 (momentVector H) := by
  have heq : pivotMatrix1047 = (fun u v => node1047 (pivotPermutation1047 u) v) := by apply Matrix.ext; unfold pivotMatrix1047 node1047 pivotPermutation1047; decide +kernel
  have hmoment : injectiveMoment H node1047 = injectiveMoment H pivotMatrix1047 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1047 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1047 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1047 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1047 (0 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1047 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1047 (1 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1047 (1 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1047 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1047 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1047 (2 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1047 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1047 + (injectiveMoment H (mergeFirst pivotMatrix1047 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1047 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1047 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1047, value185, value230, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1048 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1048 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound1048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1048 = Sparse.eval value1048 (momentVector H) := by
  have heq : pivotMatrix1048 = (fun u v => node1048 (pivotPermutation1048 u) v) := by apply Matrix.ext; unfold pivotMatrix1048 node1048 pivotPermutation1048; decide +kernel
  have hmoment : injectiveMoment H node1048 = injectiveMoment H pivotMatrix1048 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1048 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1048 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1048 (0 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1048 (0 : Fin 3) = raw6699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1048 raw6699; decide +kernel
    rw [heq]
    exact (canonical6699 hH).trans (sound293 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1048 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1048 (1 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1048 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1048 (2 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1048 (2 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1048 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1048 + (injectiveMoment H (mergeFirst pivotMatrix1048 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1048 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1048 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1048, value293, value294, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1049 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1049 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 2, -3, 1], ![1, -1, 2, -2]]

theorem sound1049 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1049 = Sparse.eval value1049 (momentVector H) := by
  have heq : pivotMatrix1049 = (fun u v => node1049 (pivotPermutation1049 u) v) := by apply Matrix.ext; unfold pivotMatrix1049 node1049 pivotPermutation1049; decide +kernel
  have hmoment : injectiveMoment H node1049 = injectiveMoment H pivotMatrix1049 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1049 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1049 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1049 (0 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1049 (0 : Fin 3) = raw6705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1049 raw6705; decide +kernel
    rw [heq]
    exact (canonical6705 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1049 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1049 (1 : Fin 3) = raw6557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1049 raw6557; decide +kernel
    rw [heq]
    exact (canonical6557 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1049 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1049 (2 : Fin 3) = raw6556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1049 raw6556; decide +kernel
    rw [heq]
    exact (canonical6556 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1049 + (injectiveMoment H (mergeFirst pivotMatrix1049 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1049 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1049 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1049, value187, value203, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1050 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1050 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem sound1050 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1050 = Sparse.eval value1050 (momentVector H) := by
  have heq : pivotMatrix1050 = (fun u v => node1050 (pivotPermutation1050 u) v) := by apply Matrix.ext; unfold pivotMatrix1050 node1050 pivotPermutation1050; decide +kernel
  have hmoment : injectiveMoment H node1050 = injectiveMoment H pivotMatrix1050 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1050 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1050 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1050 (0 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1050 (0 : Fin 3) = raw6708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1050 raw6708; decide +kernel
    rw [heq]
    exact (canonical6708 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1050 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1050 (1 : Fin 3) = raw6560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1050 raw6560; decide +kernel
    rw [heq]
    exact (canonical6560 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1050 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1050 (2 : Fin 3) = raw6559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1050 raw6559; decide +kernel
    rw [heq]
    exact (canonical6559 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1050 + (injectiveMoment H (mergeFirst pivotMatrix1050 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1050 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1050 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1050, value153, value181, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1051 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 2, -4, 2], ![2, -2, 3, -3]]

theorem sound1051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1051 = Sparse.eval value1051 (momentVector H) := by
  have heq : pivotMatrix1051 = (fun u v => node1051.transpose (pivotPermutation1051 u) v) := by apply Matrix.ext; unfold pivotMatrix1051 node1051 pivotPermutation1051; decide +kernel
  have hmoment : injectiveMoment H node1051 = injectiveMoment H pivotMatrix1051 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1051 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1051 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1051 (0 : Fin 3)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1051 (0 : Fin 3) = raw3843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1051 raw3843; decide +kernel
    rw [heq]
    exact (canonical3843 hH).trans (sound211 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1051 (1 : Fin 3)) =
      Sparse.eval value257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1051 (1 : Fin 3) = raw7476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1051 raw7476; decide +kernel
    rw [heq]
    exact (canonical7476 hH).trans (sound257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1051 (2 : Fin 3)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1051 (2 : Fin 3) = raw7509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1051 raw7509; decide +kernel
    rw [heq]
    exact (canonical7509 hH).trans (sound256 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1051 + (injectiveMoment H (mergeFirst pivotMatrix1051 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1051 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1051 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1051, value211, value256, value257, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1052 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![2, -2, 2, -2]]

theorem sound1052 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1052 = Sparse.eval value1052 (momentVector H) := by
  have heq : pivotMatrix1052 = (fun u v => node1052.transpose (pivotPermutation1052 u) v) := by apply Matrix.ext; unfold pivotMatrix1052 node1052 pivotPermutation1052; decide +kernel
  have hmoment : injectiveMoment H node1052 = injectiveMoment H pivotMatrix1052 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1052 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1052 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1052 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1052 (0 : Fin 3) = raw3845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1052 raw3845; decide +kernel
    rw [heq]
    exact (canonical3845 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1052 (1 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1052 (1 : Fin 3) = raw7477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1052 raw7477; decide +kernel
    rw [heq]
    exact (canonical7477 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1052 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1052 (2 : Fin 3) = raw7510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1052 raw7510; decide +kernel
    rw [heq]
    exact (canonical7510 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1052 + (injectiveMoment H (mergeFirst pivotMatrix1052 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1052 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1052 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1052, value212, value272, value274, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1053 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1053 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1]]

theorem sound1053 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1053 = Sparse.eval value1053 (momentVector H) := by
  have heq : pivotMatrix1053 = (fun u v => node1053 (pivotPermutation1053 u) v) := by apply Matrix.ext; unfold pivotMatrix1053 node1053 pivotPermutation1053; decide +kernel
  have hmoment : injectiveMoment H node1053 = injectiveMoment H pivotMatrix1053 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1053 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1053 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1053 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1053 (0 : Fin 3) = raw8491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1053 raw8491; decide +kernel
    rw [heq]
    exact (canonical8491 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1053 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1053 (1 : Fin 3) = raw6567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1053 raw6567; decide +kernel
    rw [heq]
    exact (canonical6567 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1053 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1053 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1053 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1053 + (injectiveMoment H (mergeFirst pivotMatrix1053 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1053 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1053 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1053, value185, value207, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1054 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1054 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![1, 0, -1, 0]]

theorem sound1054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1054 = Sparse.eval value1054 (momentVector H) := by
  have heq : pivotMatrix1054 = (fun u v => node1054 (pivotPermutation1054 u) v) := by apply Matrix.ext; unfold pivotMatrix1054 node1054 pivotPermutation1054; decide +kernel
  have hmoment : injectiveMoment H node1054 = injectiveMoment H pivotMatrix1054 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1054 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1054 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1054 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1054 (0 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1054 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1054 (1 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1054 (1 : Fin 3) = raw6546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1054 raw6546; decide +kernel
    rw [heq]
    exact (canonical6546 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1054 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1054 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1054 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1054 + (injectiveMoment H (mergeFirst pivotMatrix1054 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1054 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1054 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1054, value207, value294, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1055 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1055 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, -4, 2], ![2, -2, 2, -2]]

theorem sound1055 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1055 = Sparse.eval value1055 (momentVector H) := by
  have heq : pivotMatrix1055 = (fun u v => node1055.transpose (pivotPermutation1055 u) v) := by apply Matrix.ext; unfold pivotMatrix1055 node1055 pivotPermutation1055; decide +kernel
  have hmoment : injectiveMoment H node1055 = injectiveMoment H pivotMatrix1055 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1055 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1055 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1055 (0 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1055 (0 : Fin 3) = raw4194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1055 raw4194; decide +kernel
    rw [heq]
    exact (canonical4194 hH).trans (sound151 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1055 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1055 (1 : Fin 3) = raw7535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1055 raw7535; decide +kernel
    rw [heq]
    exact (canonical7535 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1055 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1055 (2 : Fin 3) = raw7588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1055 raw7588; decide +kernel
    rw [heq]
    exact (canonical7588 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1055 + (injectiveMoment H (mergeFirst pivotMatrix1055 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1055 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1055 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1055, value151, value152, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1056 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1056 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![2, -2, 1, -1]]

theorem sound1056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1056 = Sparse.eval value1056 (momentVector H) := by
  have heq : pivotMatrix1056 = (fun u v => node1056.transpose (pivotPermutation1056 u) v) := by apply Matrix.ext; unfold pivotMatrix1056 node1056 pivotPermutation1056; decide +kernel
  have hmoment : injectiveMoment H node1056 = injectiveMoment H pivotMatrix1056 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1056 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1056 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1056 (0 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (0 : Fin 3) = raw4195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw4195; decide +kernel
    rw [heq]
    exact (canonical4195 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1056 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (1 : Fin 3) = raw7536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw7536; decide +kernel
    rw [heq]
    exact (canonical7536 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1056 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1056 (2 : Fin 3) = raw7589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1056 raw7589; decide +kernel
    rw [heq]
    exact (canonical7589 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1056 + (injectiveMoment H (mergeFirst pivotMatrix1056 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1056 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1056 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1056, value177, value184, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1057 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1057 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0]]

theorem sound1057 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1057 = Sparse.eval value1057 (momentVector H) := by
  have heq : pivotMatrix1057 = (fun u v => node1057 (pivotPermutation1057 u) v) := by apply Matrix.ext; unfold pivotMatrix1057 node1057 pivotPermutation1057; decide +kernel
  have hmoment : injectiveMoment H node1057 = injectiveMoment H pivotMatrix1057 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1057 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1057 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1057 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1057 (0 : Fin 3) = raw8093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1057 raw8093; decide +kernel
    rw [heq]
    exact (canonical8093 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1057 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1057 (1 : Fin 3) = raw6563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1057 raw6563; decide +kernel
    rw [heq]
    exact (canonical6563 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1057 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1057 (2 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1057 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1057 + (injectiveMoment H (mergeFirst pivotMatrix1057 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1057 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1057 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1057, value203, value207, value41, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1058 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![2, -2, -1, 1]]

theorem sound1058 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1058 = Sparse.eval value1058 (momentVector H) := by
  have heq : pivotMatrix1058 = (fun u v => node1058.transpose (pivotPermutation1058 u) v) := by apply Matrix.ext; unfold pivotMatrix1058 node1058 pivotPermutation1058; decide +kernel
  have hmoment : injectiveMoment H node1058 = injectiveMoment H pivotMatrix1058 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1058 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1058 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1058 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1058 (0 : Fin 3) = raw4196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1058 raw4196; decide +kernel
    rw [heq]
    exact (canonical4196 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1058 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1058 (1 : Fin 3) = raw7538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1058 raw7538; decide +kernel
    rw [heq]
    exact (canonical7538 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1058 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1058 (2 : Fin 3) = raw7590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1058 raw7590; decide +kernel
    rw [heq]
    exact (canonical7590 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1058 + (injectiveMoment H (mergeFirst pivotMatrix1058 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1058 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1058 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1058, value203, value210, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1059 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![2, -2, -2, 2]]

theorem sound1059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1059 = Sparse.eval value1059 (momentVector H) := by
  have heq : pivotMatrix1059 = (fun u v => node1059.transpose (pivotPermutation1059 u) v) := by apply Matrix.ext; unfold pivotMatrix1059 node1059 pivotPermutation1059; decide +kernel
  have hmoment : injectiveMoment H node1059 = injectiveMoment H pivotMatrix1059 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1059 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1059 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1059 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (0 : Fin 3) = raw4197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw4197; decide +kernel
    rw [heq]
    exact (canonical4197 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1059 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (1 : Fin 3) = raw7539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw7539; decide +kernel
    rw [heq]
    exact (canonical7539 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1059 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1059 + (injectiveMoment H (mergeFirst pivotMatrix1059 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1059 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1059 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1059, value169, value197, value202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1060 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![2, -2, -3, 3]]

theorem sound1060 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1060 = Sparse.eval value1060 (momentVector H) := by
  have heq : pivotMatrix1060 = (fun u v => node1060.transpose (pivotPermutation1060 u) v) := by apply Matrix.ext; unfold pivotMatrix1060 node1060 pivotPermutation1060; decide +kernel
  have hmoment : injectiveMoment H node1060 = injectiveMoment H pivotMatrix1060 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1060 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1060 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1060 (0 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1060 (0 : Fin 3) = raw4198 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1060 raw4198; decide +kernel
    rw [heq]
    exact (canonical4198 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1060 (1 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1060 (1 : Fin 3) = raw7540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1060 raw7540; decide +kernel
    rw [heq]
    exact (canonical7540 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1060 (2 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1060 (2 : Fin 3) = raw7592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1060 raw7592; decide +kernel
    rw [heq]
    exact (canonical7592 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1060 + (injectiveMoment H (mergeFirst pivotMatrix1060 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1060 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1060 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1060, value163, value166, value167, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1061 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1061 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 3, -4, 1], ![2, -3, 3, -2]]

theorem sound1061 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1061 = Sparse.eval value1061 (momentVector H) := by
  have heq : pivotMatrix1061 = (fun u v => node1061.transpose (pivotPermutation1061 u) v) := by apply Matrix.ext; unfold pivotMatrix1061 node1061 pivotPermutation1061; decide +kernel
  have hmoment : injectiveMoment H node1061 = injectiveMoment H pivotMatrix1061 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1061 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1061 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1061 (0 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1061 (0 : Fin 3) = raw3852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1061 raw3852; decide +kernel
    rw [heq]
    exact (canonical3852 hH).trans (sound213 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1061 (1 : Fin 3)) =
      Sparse.eval value257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1061 (1 : Fin 3) = raw7479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1061 raw7479; decide +kernel
    rw [heq]
    exact (canonical7479 hH).trans (sound257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1061 (2 : Fin 3)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1061 (2 : Fin 3) = raw7513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1061 raw7513; decide +kernel
    rw [heq]
    exact (canonical7513 hH).trans (sound255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1061 + (injectiveMoment H (mergeFirst pivotMatrix1061 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1061 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1061 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1061, value213, value255, value257, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1062 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1062 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2]]

theorem sound1062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1062 = Sparse.eval value1062 (momentVector H) := by
  have heq : pivotMatrix1062 = (fun u v => node1062 (pivotPermutation1062 u) v) := by apply Matrix.ext; unfold pivotMatrix1062 node1062 pivotPermutation1062; decide +kernel
  have hmoment : injectiveMoment H node1062 = injectiveMoment H pivotMatrix1062 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1062 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1062 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1062 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1062 (0 : Fin 3) = raw8501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1062 raw8501; decide +kernel
    rw [heq]
    exact (canonical8501 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1062 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1062 (1 : Fin 3) = raw6568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1062 raw6568; decide +kernel
    rw [heq]
    exact (canonical6568 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1062 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1062 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1062 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1062 + (injectiveMoment H (mergeFirst pivotMatrix1062 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1062 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1062 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1062, value155, value188, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1063 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1063 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

theorem sound1063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1063 = Sparse.eval value1063 (momentVector H) := by
  have heq : pivotMatrix1063 = (fun u v => node1063 (pivotPermutation1063 u) v) := by apply Matrix.ext; unfold pivotMatrix1063 node1063 pivotPermutation1063; decide +kernel
  have hmoment : injectiveMoment H node1063 = injectiveMoment H pivotMatrix1063 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1063 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1063 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1063 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1063 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (1 : Fin 3) = raw6567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw6567; decide +kernel
    rw [heq]
    exact (canonical6567 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1063 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1063 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1063 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1063 + (injectiveMoment H (mergeFirst pivotMatrix1063 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1063 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1063 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1063, value185, value188, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1064 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, -4, 1], ![2, -3, 2, -1]]

theorem sound1064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1064 = Sparse.eval value1064 (momentVector H) := by
  have heq : pivotMatrix1064 = (fun u v => node1064.transpose (pivotPermutation1064 u) v) := by apply Matrix.ext; unfold pivotMatrix1064 node1064 pivotPermutation1064; decide +kernel
  have hmoment : injectiveMoment H node1064 = injectiveMoment H pivotMatrix1064 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1064 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1064 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1064 (0 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1064 (0 : Fin 3) = raw4199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1064 raw4199; decide +kernel
    rw [heq]
    exact (canonical4199 hH).trans (sound147 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1064 (1 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1064 (1 : Fin 3) = raw7541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1064 raw7541; decide +kernel
    rw [heq]
    exact (canonical7541 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1064 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1064 (2 : Fin 3) = raw7593 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1064 raw7593; decide +kernel
    rw [heq]
    exact (canonical7593 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1064 + (injectiveMoment H (mergeFirst pivotMatrix1064 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1064 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1064 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1064, value147, value154, value155, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1065 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1065 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1]]

theorem sound1065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1065 = Sparse.eval value1065 (momentVector H) := by
  have heq : pivotMatrix1065 = (fun u v => node1065 (pivotPermutation1065 u) v) := by apply Matrix.ext; unfold pivotMatrix1065 node1065 pivotPermutation1065; decide +kernel
  have hmoment : injectiveMoment H node1065 = injectiveMoment H pivotMatrix1065 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1065 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1065 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1065 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1065 (0 : Fin 3) = raw8097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1065 raw8097; decide +kernel
    rw [heq]
    exact (canonical8097 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1065 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1065 (1 : Fin 3) = raw6564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1065 raw6564; decide +kernel
    rw [heq]
    exact (canonical6564 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1065 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1065 (2 : Fin 3) = raw6519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1065 raw6519; decide +kernel
    rw [heq]
    exact (canonical6519 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1065 + (injectiveMoment H (mergeFirst pivotMatrix1065 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1065 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1065 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1065, value187, value188, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1066 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, -2, -1], ![2, -3, 0, 1]]

theorem sound1066 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1066 = Sparse.eval value1066 (momentVector H) := by
  have heq : pivotMatrix1066 = (fun u v => node1066.transpose (pivotPermutation1066 u) v) := by apply Matrix.ext; unfold pivotMatrix1066 node1066 pivotPermutation1066; decide +kernel
  have hmoment : injectiveMoment H node1066 = injectiveMoment H pivotMatrix1066 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1066 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1066 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1066 (0 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1066 (0 : Fin 3) = raw4200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1066 raw4200; decide +kernel
    rw [heq]
    exact (canonical4200 hH).trans (sound204 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1066 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1066 (1 : Fin 3) = raw7542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1066 raw7542; decide +kernel
    rw [heq]
    exact (canonical7542 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1066 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1066 (2 : Fin 3) = raw7594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1066 raw7594; decide +kernel
    rw [heq]
    exact (canonical7594 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1066 + (injectiveMoment H (mergeFirst pivotMatrix1066 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1066 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1066 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1066, value204, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1067 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, -1, -2], ![2, -3, -1, 2]]

theorem sound1067 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1067 = Sparse.eval value1067 (momentVector H) := by
  have heq : pivotMatrix1067 = (fun u v => node1067.transpose (pivotPermutation1067 u) v) := by apply Matrix.ext; unfold pivotMatrix1067 node1067 pivotPermutation1067; decide +kernel
  have hmoment : injectiveMoment H node1067 = injectiveMoment H pivotMatrix1067 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1067 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1067 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1067 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1067 (0 : Fin 3) = raw4201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1067 raw4201; decide +kernel
    rw [heq]
    exact (canonical4201 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1067 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1067 (1 : Fin 3) = raw7543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1067 raw7543; decide +kernel
    rw [heq]
    exact (canonical7543 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1067 (2 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1067 (2 : Fin 3) = raw7595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1067 raw7595; decide +kernel
    rw [heq]
    exact (canonical7595 hH).trans (sound222 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1067 + (injectiveMoment H (mergeFirst pivotMatrix1067 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1067 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1067 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1067, value198, value222, value223, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1068 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 3, 0, -3], ![2, -3, -2, 3]]

theorem sound1068 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1068 = Sparse.eval value1068 (momentVector H) := by
  have heq : pivotMatrix1068 = (fun u v => node1068.transpose (pivotPermutation1068 u) v) := by apply Matrix.ext; unfold pivotMatrix1068 node1068 pivotPermutation1068; decide +kernel
  have hmoment : injectiveMoment H node1068 = injectiveMoment H pivotMatrix1068 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1068 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1068 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1068 (0 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1068 (0 : Fin 3) = raw4202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1068 raw4202; decide +kernel
    rw [heq]
    exact (canonical4202 hH).trans (sound192 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1068 (1 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1068 (1 : Fin 3) = raw7544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1068 raw7544; decide +kernel
    rw [heq]
    exact (canonical7544 hH).trans (sound196 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1068 (2 : Fin 3)) =
      Sparse.eval value195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1068 (2 : Fin 3) = raw7596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1068 raw7596; decide +kernel
    rw [heq]
    exact (canonical7596 hH).trans (sound195 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1068 + (injectiveMoment H (mergeFirst pivotMatrix1068 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1068 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1068 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1068, value192, value195, value196, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1069 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1069 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2]]

theorem sound1069 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1069 = Sparse.eval value1069 (momentVector H) := by
  have heq : pivotMatrix1069 = (fun u v => node1069 (pivotPermutation1069 u) v) := by apply Matrix.ext; unfold pivotMatrix1069 node1069 pivotPermutation1069; decide +kernel
  have hmoment : injectiveMoment H node1069 = injectiveMoment H pivotMatrix1069 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1069 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1069 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1069 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1069 (0 : Fin 3) = raw8338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1069 raw8338; decide +kernel
    rw [heq]
    exact (canonical8338 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1069 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1069 (1 : Fin 3) = raw6568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1069 raw6568; decide +kernel
    rw [heq]
    exact (canonical6568 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1069 (2 : Fin 3)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1069 (2 : Fin 3) = raw6520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1069 raw6520; decide +kernel
    rw [heq]
    exact (canonical6520 hH).trans (sound157 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1069 + (injectiveMoment H (mergeFirst pivotMatrix1069 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1069 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1069 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1069, value155, value157, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1070 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, 4, -2, -2], ![2, -4, 1, 1]]

theorem sound1070 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1070 = Sparse.eval value1070 (momentVector H) := by
  have heq : pivotMatrix1070 = (fun u v => node1070.transpose (pivotPermutation1070 u) v) := by apply Matrix.ext; unfold pivotMatrix1070 node1070 pivotPermutation1070; decide +kernel
  have hmoment : injectiveMoment H node1070 = injectiveMoment H pivotMatrix1070 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1070 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1070 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1070 (0 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1070 (0 : Fin 3) = raw3854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1070 raw3854; decide +kernel
    rw [heq]
    exact (canonical3854 hH).trans (sound218 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1070 (1 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1070 (1 : Fin 3) = raw7480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1070 raw7480; decide +kernel
    rw [heq]
    exact (canonical7480 hH).trans (sound286 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1070 (2 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1070 (2 : Fin 3) = raw7514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1070 raw7514; decide +kernel
    rw [heq]
    exact (canonical7514 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1070 + (injectiveMoment H (mergeFirst pivotMatrix1070 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1070 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1070 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1070, value218, value281, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1071 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![0, 4, -3, -1], ![2, -4, 1, 1]]

theorem sound1071 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1071 = Sparse.eval value1071 (momentVector H) := by
  have heq : pivotMatrix1071 = (fun u v => node1071.transpose (pivotPermutation1071 u) v) := by apply Matrix.ext; unfold pivotMatrix1071 node1071 pivotPermutation1071; decide +kernel
  have hmoment : injectiveMoment H node1071 = injectiveMoment H pivotMatrix1071 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1071 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1071 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1071 (0 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1071 (0 : Fin 3) = raw4203 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1071 raw4203; decide +kernel
    rw [heq]
    exact (canonical4203 hH).trans (sound171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1071 (1 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1071 (1 : Fin 3) = raw7545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1071 raw7545; decide +kernel
    rw [heq]
    exact (canonical7545 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1071 (2 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1071 (2 : Fin 3) = raw7597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1071 raw7597; decide +kernel
    rw [heq]
    exact (canonical7597 hH).trans (sound190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1071 + (injectiveMoment H (mergeFirst pivotMatrix1071 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1071 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1071 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1071, value171, value190, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1072 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 1, -3, 2], ![1, -1, 3, -3]]

theorem sound1072 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1072 = Sparse.eval value1072 (momentVector H) := by
  have heq : pivotMatrix1072 = (fun u v => node1072 (pivotPermutation1072 u) v) := by apply Matrix.ext; unfold pivotMatrix1072 node1072 pivotPermutation1072; decide +kernel
  have hmoment : injectiveMoment H node1072 = injectiveMoment H pivotMatrix1072 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1072 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1072 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1072 (0 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1072 (0 : Fin 3) = raw7352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1072 raw7352; decide +kernel
    rw [heq]
    exact (canonical7352 hH).trans (sound269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1072 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1072 (1 : Fin 3) = raw6556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1072 raw6556; decide +kernel
    rw [heq]
    exact (canonical6556 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1072 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1072 (2 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1072 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1072 + (injectiveMoment H (mergeFirst pivotMatrix1072 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1072 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1072 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1072, value155, value187, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1073 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1073 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -3, 1, 2], ![2, 2, -2, -2]]

theorem sound1073 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1073 = Sparse.eval value1073 (momentVector H) := by
  have heq : pivotMatrix1073 = (fun u v => node1073.transpose (pivotPermutation1073 u) v) := by apply Matrix.ext; unfold pivotMatrix1073 node1073 pivotPermutation1073; decide +kernel
  have hmoment : injectiveMoment H node1073 = injectiveMoment H pivotMatrix1073 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1073 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1073 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1073 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1073 (0 : Fin 3) = raw4975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1073 raw4975; decide +kernel
    rw [heq]
    exact (canonical4975 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1073 (1 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1073 (1 : Fin 3) = raw7909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1073 raw7909; decide +kernel
    rw [heq]
    exact (canonical7909 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1073 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1073 (2 : Fin 3) = raw7919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1073 raw7919; decide +kernel
    rw [heq]
    exact (canonical7919 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1073 + (injectiveMoment H (mergeFirst pivotMatrix1073 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1073 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1073 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1073, value212, value260, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1074 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -3, 2, 1], ![2, 2, -3, -1]]

theorem sound1074 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1074 = Sparse.eval value1074 (momentVector H) := by
  have heq : pivotMatrix1074 = (fun u v => node1074.transpose (pivotPermutation1074 u) v) := by apply Matrix.ext; unfold pivotMatrix1074 node1074 pivotPermutation1074; decide +kernel
  have hmoment : injectiveMoment H node1074 = injectiveMoment H pivotMatrix1074 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1074 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1074 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1074 (0 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1074 (0 : Fin 3) = raw4976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1074 raw4976; decide +kernel
    rw [heq]
    exact (canonical4976 hH).trans (sound209 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1074 (1 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1074 (1 : Fin 3) = raw7910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1074 raw7910; decide +kernel
    rw [heq]
    exact (canonical7910 hH).trans (sound262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1074 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1074 (2 : Fin 3) = raw7920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1074 raw7920; decide +kernel
    rw [heq]
    exact (canonical7920 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1074 + (injectiveMoment H (mergeFirst pivotMatrix1074 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1074 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1074 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1074, value209, value262, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1075 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1075 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4]]

theorem sound1075 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1075 = Sparse.eval value1075 (momentVector H) := by
  have heq : pivotMatrix1075 = (fun u v => node1075 (pivotPermutation1075 u) v) := by apply Matrix.ext; unfold pivotMatrix1075 node1075 pivotPermutation1075; decide +kernel
  have hmoment : injectiveMoment H node1075 = injectiveMoment H pivotMatrix1075 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1075 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1075 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1075 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1075 (0 : Fin 3) = raw8098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1075 raw8098; decide +kernel
    rw [heq]
    exact (canonical8098 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1075 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1075 (1 : Fin 3) = raw6565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1075 raw6565; decide +kernel
    rw [heq]
    exact (canonical6565 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1075 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1075 (2 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1075 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1075 + (injectiveMoment H (mergeFirst pivotMatrix1075 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1075 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1075 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1075, value155, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1076 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![0, -3, 2, 1], ![2, 2, -4, 0]]

theorem sound1076 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1076 = Sparse.eval value1076 (momentVector H) := by
  have heq : pivotMatrix1076 = (fun u v => node1076.transpose (pivotPermutation1076 u) v) := by apply Matrix.ext; unfold pivotMatrix1076 node1076 pivotPermutation1076; decide +kernel
  have hmoment : injectiveMoment H node1076 = injectiveMoment H pivotMatrix1076 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1076 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1076 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1076 (0 : Fin 3)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1076 (0 : Fin 3) = raw5053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1076 raw5053; decide +kernel
    rw [heq]
    exact (canonical5053 hH).trans (sound102 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1076 (1 : Fin 3)) =
      Sparse.eval value136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1076 (1 : Fin 3) = raw7943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1076 raw7943; decide +kernel
    rw [heq]
    exact (canonical7943 hH).trans (sound136 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1076 (2 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1076 (2 : Fin 3) = raw7946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1076 raw7946; decide +kernel
    rw [heq]
    exact (canonical7946 hH).trans (sound106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1076 + (injectiveMoment H (mergeFirst pivotMatrix1076 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1076 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1076 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1076, value102, value106, value136, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1077 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, -2, 4], ![2, 1, 1, -4]]

theorem sound1077 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1077 = Sparse.eval value1077 (momentVector H) := by
  have heq : pivotMatrix1077 = (fun u v => node1077.transpose (pivotPermutation1077 u) v) := by apply Matrix.ext; unfold pivotMatrix1077 node1077 pivotPermutation1077; decide +kernel
  have hmoment : injectiveMoment H node1077 = injectiveMoment H pivotMatrix1077 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1077 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1077 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1077 (0 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1077 (0 : Fin 3) = raw4977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1077 raw4977; decide +kernel
    rw [heq]
    exact (canonical4977 hH).trans (sound218 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1077 (1 : Fin 3)) =
      Sparse.eval value234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1077 (1 : Fin 3) = raw7912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1077 raw7912; decide +kernel
    rw [heq]
    exact (canonical7912 hH).trans (sound234 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1077 (2 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1077 (2 : Fin 3) = raw7921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1077 raw7921; decide +kernel
    rw [heq]
    exact (canonical7921 hH).trans (sound244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1077 + (injectiveMoment H (mergeFirst pivotMatrix1077 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1077 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1077 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1077, value218, value234, value244, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1078 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, 1, 1], ![2, 1, -2, -1]]

theorem sound1078 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1078 = Sparse.eval value1078 (momentVector H) := by
  have heq : pivotMatrix1078 = (fun u v => node1078.transpose (pivotPermutation1078 u) v) := by apply Matrix.ext; unfold pivotMatrix1078 node1078 pivotPermutation1078; decide +kernel
  have hmoment : injectiveMoment H node1078 = injectiveMoment H pivotMatrix1078 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1078 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1078 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1078 (0 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1078 (0 : Fin 3) = raw4981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1078 raw4981; decide +kernel
    rw [heq]
    exact (canonical4981 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1078 (1 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1078 (1 : Fin 3) = raw7913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1078 raw7913; decide +kernel
    rw [heq]
    exact (canonical7913 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1078 (2 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1078 (2 : Fin 3) = raw7922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1078 raw7922; decide +kernel
    rw [heq]
    exact (canonical7922 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1078 + (injectiveMoment H (mergeFirst pivotMatrix1078 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1078 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1078 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1078, value210, value230, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1079 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1079 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

theorem sound1079 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1079 = Sparse.eval value1079 (momentVector H) := by
  have heq : pivotMatrix1079 = (fun u v => node1079 (pivotPermutation1079 u) v) := by apply Matrix.ext; unfold pivotMatrix1079 node1079 pivotPermutation1079; decide +kernel
  have hmoment : injectiveMoment H node1079 = injectiveMoment H pivotMatrix1079 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1079 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1079 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1079 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (0 : Fin 3) = raw8099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw8099; decide +kernel
    rw [heq]
    exact (canonical8099 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1079 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (1 : Fin 3) = raw6566 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw6566; decide +kernel
    rw [heq]
    exact (canonical6566 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1079 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (2 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1079 + (injectiveMoment H (mergeFirst pivotMatrix1079 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1079 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1079 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1079, value185, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1080 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![2, 1, -4, 1]]

theorem sound1080 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1080 = Sparse.eval value1080 (momentVector H) := by
  have heq : pivotMatrix1080 = (fun u v => node1080.transpose (pivotPermutation1080 u) v) := by apply Matrix.ext; unfold pivotMatrix1080 node1080 pivotPermutation1080; decide +kernel
  have hmoment : injectiveMoment H node1080 = injectiveMoment H pivotMatrix1080 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1080 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1080 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1080 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1080 (0 : Fin 3) = raw4982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1080 raw4982; decide +kernel
    rw [heq]
    exact (canonical4982 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1080 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1080 (1 : Fin 3) = raw7915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1080 raw7915; decide +kernel
    rw [heq]
    exact (canonical7915 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1080 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1080 (2 : Fin 3) = raw7923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1080 raw7923; decide +kernel
    rw [heq]
    exact (canonical7923 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1080 + (injectiveMoment H (mergeFirst pivotMatrix1080 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1080 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1080 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1080, value206, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1081 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1081 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem sound1081 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1081 = Sparse.eval value1081 (momentVector H) := by
  have heq : pivotMatrix1081 = (fun u v => node1081 (pivotPermutation1081 u) v) := by apply Matrix.ext; unfold pivotMatrix1081 node1081 pivotPermutation1081; decide +kernel
  have hmoment : injectiveMoment H node1081 = injectiveMoment H pivotMatrix1081 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1081 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1081 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1081 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1081 (0 : Fin 3) = raw7245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1081 raw7245; decide +kernel
    rw [heq]
    exact (canonical7245 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1081 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1081 (1 : Fin 3) = raw6559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1081 raw6559; decide +kernel
    rw [heq]
    exact (canonical6559 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1081 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1081 (2 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1081 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1081 + (injectiveMoment H (mergeFirst pivotMatrix1081 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1081 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1081 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1081, value181, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1082 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, -1, -2, 2]]

theorem sound1082 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1082 = Sparse.eval value1082 (momentVector H) := by
  have heq : pivotMatrix1082 = (fun u v => node1082 (pivotPermutation1082 u) v) := by apply Matrix.ext; unfold pivotMatrix1082 node1082 pivotPermutation1082; decide +kernel
  have hmoment : injectiveMoment H node1082 = injectiveMoment H pivotMatrix1082 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1082 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1082 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1082 (0 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1082 (0 : Fin 3) = raw7246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1082 raw7246; decide +kernel
    rw [heq]
    exact (canonical7246 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1082 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1082 (1 : Fin 3) = raw6560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1082 raw6560; decide +kernel
    rw [heq]
    exact (canonical6560 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1082 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1082 (2 : Fin 3) = raw6555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1082 raw6555; decide +kernel
    rw [heq]
    exact (canonical6555 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1082 + (injectiveMoment H (mergeFirst pivotMatrix1082 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1082 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1082 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1082, value149, value153, value155, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1083 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1083 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

theorem sound1083 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1083 = Sparse.eval value1083 (momentVector H) := by
  have heq : pivotMatrix1083 = (fun u v => node1083 (pivotPermutation1083 u) v) := by apply Matrix.ext; unfold pivotMatrix1083 node1083 pivotPermutation1083; decide +kernel
  have hmoment : injectiveMoment H node1083 = injectiveMoment H pivotMatrix1083 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1083 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1083 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1083 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1083 (0 : Fin 3) = raw7356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1083 raw7356; decide +kernel
    rw [heq]
    exact (canonical7356 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1083 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1083 (1 : Fin 3) = raw6560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1083 raw6560; decide +kernel
    rw [heq]
    exact (canonical6560 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1083 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1083 (2 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1083 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1083 + (injectiveMoment H (mergeFirst pivotMatrix1083 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1083 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1083 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1083, value153, value185, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1084 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

theorem sound1084 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1084 = Sparse.eval value1084 (momentVector H) := by
  have heq : pivotMatrix1084 = (fun u v => node1084.transpose (pivotPermutation1084 u) v) := by apply Matrix.ext; unfold pivotMatrix1084 node1084 pivotPermutation1084; decide +kernel
  have hmoment : injectiveMoment H node1084 = injectiveMoment H pivotMatrix1084 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1084 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1084 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1084 (0 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1084 (0 : Fin 3) = raw5041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1084 raw5041; decide +kernel
    rw [heq]
    exact (canonical5041 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1084 (1 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1084 (1 : Fin 3) = raw7916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1084 raw7916; decide +kernel
    rw [heq]
    exact (canonical7916 hH).trans (sound275 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1084 (2 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1084 (2 : Fin 3) = raw7938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1084 raw7938; decide +kernel
    rw [heq]
    exact (canonical7938 hH).trans (sound175 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1084 + (injectiveMoment H (mergeFirst pivotMatrix1084 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1084 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1084 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1084, value175, value202, value275, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1085 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![2, -2, -3, 3]]

theorem sound1085 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1085 = Sparse.eval value1085 (momentVector H) := by
  have heq : pivotMatrix1085 = (fun u v => node1085.transpose (pivotPermutation1085 u) v) := by apply Matrix.ext; unfold pivotMatrix1085 node1085 pivotPermutation1085; decide +kernel
  have hmoment : injectiveMoment H node1085 = injectiveMoment H pivotMatrix1085 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1085 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1085 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1085 (0 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1085 (0 : Fin 3) = raw5042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1085 raw5042; decide +kernel
    rw [heq]
    exact (canonical5042 hH).trans (sound196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1085 (1 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1085 (1 : Fin 3) = raw7917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1085 raw7917; decide +kernel
    rw [heq]
    exact (canonical7917 hH).trans (sound258 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1085 (2 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1085 (2 : Fin 3) = raw7939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1085 raw7939; decide +kernel
    rw [heq]
    exact (canonical7939 hH).trans (sound241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1085 + (injectiveMoment H (mergeFirst pivotMatrix1085 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1085 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1085 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1085, value196, value241, value258, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1086 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![0, 3, -3, 0], ![2, -4, 1, 1]]

theorem sound1086 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1086 = Sparse.eval value1086 (momentVector H) := by
  have heq : pivotMatrix1086 = (fun u v => node1086.transpose (pivotPermutation1086 u) v) := by apply Matrix.ext; unfold pivotMatrix1086 node1086 pivotPermutation1086; decide +kernel
  have hmoment : injectiveMoment H node1086 = injectiveMoment H pivotMatrix1086 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1086 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1086 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1086 (0 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1086 (0 : Fin 3) = raw5069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1086 raw5069; decide +kernel
    rw [heq]
    exact (canonical5069 hH).trans (sound81 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1086 (1 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1086 (1 : Fin 3) = raw7944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1086 raw7944; decide +kernel
    rw [heq]
    exact (canonical7944 hH).trans (sound161 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1086 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1086 (2 : Fin 3) = raw7952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1086 raw7952; decide +kernel
    rw [heq]
    exact (canonical7952 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1086 + (injectiveMoment H (mergeFirst pivotMatrix1086 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1086 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1086 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1086, value161, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1087 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![0, 3, -2, -1], ![2, -4, 0, 2]]

theorem sound1087 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1087 = Sparse.eval value1087 (momentVector H) := by
  have heq : pivotMatrix1087 = (fun u v => node1087.transpose (pivotPermutation1087 u) v) := by apply Matrix.ext; unfold pivotMatrix1087 node1087 pivotPermutation1087; decide +kernel
  have hmoment : injectiveMoment H node1087 = injectiveMoment H pivotMatrix1087 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1087 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1087 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1087 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1087 (0 : Fin 3) = raw5070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1087 raw5070; decide +kernel
    rw [heq]
    exact (canonical5070 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1087 (1 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1087 (1 : Fin 3) = raw7945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1087 raw7945; decide +kernel
    rw [heq]
    exact (canonical7945 hH).trans (sound85 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1087 (2 : Fin 3)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1087 (2 : Fin 3) = raw7953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1087 raw7953; decide +kernel
    rw [heq]
    exact (canonical7953 hH).trans (sound83 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1087 + (injectiveMoment H (mergeFirst pivotMatrix1087 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1087 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1087 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1087, value83, value85, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
