import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical124
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical125
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node512 = Sparse.eval value512 (momentVector H) := by
  have hc : momentVector H 460 = injectiveMoment H node512 := rfl
  simp [value512, Sparse.eval, hc]

theorem sound513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node513 = Sparse.eval value513 (momentVector H) := by
  have hc : momentVector H 44 = injectiveMoment H node513 := rfl
  simp [value513, Sparse.eval, hc]

theorem sound514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node514 = Sparse.eval value514 (momentVector H) := by
  have hc : momentVector H 45 = injectiveMoment H node514 := rfl
  simp [value514, Sparse.eval, hc]

theorem sound515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node515 = Sparse.eval value515 (momentVector H) := by
  have hc : momentVector H 119 = injectiveMoment H node515 := rfl
  simp [value515, Sparse.eval, hc]

theorem sound516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node516 = Sparse.eval value516 (momentVector H) := by
  have hc : momentVector H 120 = injectiveMoment H node516 := rfl
  simp [value516, Sparse.eval, hc]

theorem sound517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node517 = Sparse.eval value517 (momentVector H) := by
  have hc : momentVector H 46 = injectiveMoment H node517 := rfl
  simp [value517, Sparse.eval, hc]

theorem sound518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node518 = Sparse.eval value518 (momentVector H) := by
  have hc : momentVector H 122 = injectiveMoment H node518 := rfl
  simp [value518, Sparse.eval, hc]

theorem sound519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node519 = Sparse.eval value519 (momentVector H) := by
  have hc : momentVector H 472 = injectiveMoment H node519 := rfl
  simp [value519, Sparse.eval, hc]

theorem sound520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node520 = Sparse.eval value520 (momentVector H) := by
  have hc : momentVector H 47 = injectiveMoment H node520 := rfl
  simp [value520, Sparse.eval, hc]

theorem sound521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node521 = Sparse.eval value521 (momentVector H) := by
  have hc : momentVector H 48 = injectiveMoment H node521 := rfl
  simp [value521, Sparse.eval, hc]

theorem sound522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node522 = Sparse.eval value522 (momentVector H) := by
  have hc : momentVector H 49 = injectiveMoment H node522 := rfl
  simp [value522, Sparse.eval, hc]

theorem sound523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node523 = Sparse.eval value523 (momentVector H) := by
  have hc : momentVector H 50 = injectiveMoment H node523 := rfl
  simp [value523, Sparse.eval, hc]

def pivotPermutation524 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

theorem sound524 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node524 = Sparse.eval value524 (momentVector H) := by
  have heq : pivotMatrix524 = (fun u v => node524 (pivotPermutation524 u) v) := by apply Matrix.ext; unfold pivotMatrix524 node524 pivotPermutation524; decide +kernel
  have hmoment : injectiveMoment H node524 = injectiveMoment H pivotMatrix524 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix524 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix524 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix524 (0 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix524 (0 : Fin 4) = raw3906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix524 raw3906; decide +kernel
    rw [heq]
    exact (canonical3906 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix524 (1 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix524 (1 : Fin 4) = raw2666 := by apply Matrix.ext; unfold mergeFirst pivotMatrix524 raw2666; decide +kernel
    rw [heq]
    exact (canonical2666 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix524 (2 : Fin 4)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix524 (2 : Fin 4) = raw2661 := by apply Matrix.ext; unfold mergeFirst pivotMatrix524 raw2661; decide +kernel
    rw [heq]
    exact (canonical2661 hH).trans (sound89 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix524 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix524 (3 : Fin 4) = raw2660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix524 raw2660; decide +kernel
    rw [heq]
    exact (canonical2660 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node524 + (injectiveMoment H (mergeFirst pivotMatrix524 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix524 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix524 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix524 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value524, value167, value180, value184, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation525 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix525 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![2, 1, -3]]

theorem sound525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node525 = Sparse.eval value525 (momentVector H) := by
  have heq : pivotMatrix525 = (fun u v => node525 (pivotPermutation525 u) v) := by apply Matrix.ext; unfold pivotMatrix525 node525 pivotPermutation525; decide +kernel
  have hmoment : injectiveMoment H node525 = injectiveMoment H pivotMatrix525 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix525 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix525 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix525 (0 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix525 (0 : Fin 4) = raw5857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix525 raw5857; decide +kernel
    rw [heq]
    exact (canonical5857 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix525 (1 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix525 (1 : Fin 4) = raw2718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix525 raw2718; decide +kernel
    rw [heq]
    exact (canonical2718 hH).trans (sound162 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix525 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix525 (2 : Fin 4) = raw2659 := by apply Matrix.ext; unfold mergeFirst pivotMatrix525 raw2659; decide +kernel
    rw [heq]
    exact (canonical2659 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix525 (3 : Fin 4)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix525 (3 : Fin 4) = raw2657 := by apply Matrix.ext; unfold mergeFirst pivotMatrix525 raw2657; decide +kernel
    rw [heq]
    exact (canonical2657 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node525 + (injectiveMoment H (mergeFirst pivotMatrix525 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix525 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix525 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix525 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value525, value162, value167, value196, value258, Sparse.eval] at hc ⊢
  linarith

theorem sound526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node526 = Sparse.eval value526 (momentVector H) := by
  have hc : momentVector H 486 = injectiveMoment H node526 := rfl
  simp [value526, Sparse.eval, hc]

def pivotPermutation527 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix527 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem sound527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node527 = Sparse.eval value527 (momentVector H) := by
  have heq : pivotMatrix527 = (fun u v => node527 (pivotPermutation527 u) v) := by apply Matrix.ext; unfold pivotMatrix527 node527 pivotPermutation527; decide +kernel
  have hmoment : injectiveMoment H node527 = injectiveMoment H pivotMatrix527 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix527 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix527 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix527 (0 : Fin 4)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix527 (0 : Fin 4) = raw298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix527 raw298; decide +kernel
    rw [heq]
    exact (canonical298 hH).trans (sound83 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix527 (1 : Fin 4)) =
      Sparse.eval value105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix527 (1 : Fin 4) = raw2673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix527 raw2673; decide +kernel
    rw [heq]
    exact (canonical2673 hH).trans (sound105 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix527 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix527 (2 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix527 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix527 (3 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix527 (3 : Fin 4) = raw2822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix527 raw2822; decide +kernel
    rw [heq]
    exact (canonical2822 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node527 + (injectiveMoment H (mergeFirst pivotMatrix527 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix527 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix527 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix527 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value527, value105, value177, value180, value83, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation528 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem sound528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node528 = Sparse.eval value528 (momentVector H) := by
  have heq : pivotMatrix528 = (fun u v => node528 (pivotPermutation528 u) v) := by apply Matrix.ext; unfold pivotMatrix528 node528 pivotPermutation528; decide +kernel
  have hmoment : injectiveMoment H node528 = injectiveMoment H pivotMatrix528 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix528 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix528 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix528 (0 : Fin 4)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix528 (0 : Fin 4) = raw304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix528 raw304; decide +kernel
    rw [heq]
    exact (canonical304 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix528 (1 : Fin 4)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix528 (1 : Fin 4) = raw2687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix528 raw2687; decide +kernel
    rw [heq]
    exact (canonical2687 hH).trans (sound159 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix528 (2 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix528 (2 : Fin 4) = raw2825 := by apply Matrix.ext; unfold mergeFirst pivotMatrix528 raw2825; decide +kernel
    rw [heq]
    exact (canonical2825 hH).trans (sound162 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix528 (3 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix528 (3 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix528 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node528 + (injectiveMoment H (mergeFirst pivotMatrix528 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix528 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix528 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix528 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value528, value159, value162, value184, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation529 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix529 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem sound529 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node529 = Sparse.eval value529 (momentVector H) := by
  have heq : pivotMatrix529 = (fun u v => node529 (pivotPermutation529 u) v) := by apply Matrix.ext; unfold pivotMatrix529 node529 pivotPermutation529; decide +kernel
  have hmoment : injectiveMoment H node529 = injectiveMoment H pivotMatrix529 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix529 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix529 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix529 (0 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix529 (0 : Fin 4) = raw310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix529 raw310; decide +kernel
    rw [heq]
    exact (canonical310 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix529 (1 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix529 (1 : Fin 4) = raw2693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix529 raw2693; decide +kernel
    rw [heq]
    exact (canonical2693 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix529 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix529 (2 : Fin 4) = raw2833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix529 raw2833; decide +kernel
    rw [heq]
    exact (canonical2833 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix529 (3 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix529 (3 : Fin 4) = raw2844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix529 raw2844; decide +kernel
    rw [heq]
    exact (canonical2844 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node529 + (injectiveMoment H (mergeFirst pivotMatrix529 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix529 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix529 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix529 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value529, value111, value177, value184, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation530 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix530 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

theorem sound530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node530 = Sparse.eval value530 (momentVector H) := by
  have heq : pivotMatrix530 = (fun u v => node530 (pivotPermutation530 u) v) := by apply Matrix.ext; unfold pivotMatrix530 node530 pivotPermutation530; decide +kernel
  have hmoment : injectiveMoment H node530 = injectiveMoment H pivotMatrix530 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix530 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix530 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix530 (0 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix530 (0 : Fin 4) = raw484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix530 raw484; decide +kernel
    rw [heq]
    exact (canonical484 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix530 (1 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix530 (1 : Fin 4) = raw2660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix530 raw2660; decide +kernel
    rw [heq]
    exact (canonical2660 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix530 (2 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix530 (2 : Fin 4) = raw2721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix530 raw2721; decide +kernel
    rw [heq]
    exact (canonical2721 hH).trans (sound163 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix530 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix530 (3 : Fin 4) = raw2727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix530 raw2727; decide +kernel
    rw [heq]
    exact (canonical2727 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node530 + (injectiveMoment H (mergeFirst pivotMatrix530 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix530 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix530 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix530 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value530, value163, value167, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation531 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

theorem sound531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node531 = Sparse.eval value531 (momentVector H) := by
  have heq : pivotMatrix531 = (fun u v => node531 (pivotPermutation531 u) v) := by apply Matrix.ext; unfold pivotMatrix531 node531 pivotPermutation531; decide +kernel
  have hmoment : injectiveMoment H node531 = injectiveMoment H pivotMatrix531 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix531 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix531 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix531 (0 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix531 (0 : Fin 4) = raw506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix531 raw506; decide +kernel
    rw [heq]
    exact (canonical506 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix531 (1 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix531 (1 : Fin 4) = raw2666 := by apply Matrix.ext; unfold mergeFirst pivotMatrix531 raw2666; decide +kernel
    rw [heq]
    exact (canonical2666 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix531 (2 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix531 (2 : Fin 4) = raw2759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix531 raw2759; decide +kernel
    rw [heq]
    exact (canonical2759 hH).trans (sound170 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix531 (3 : Fin 4)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix531 (3 : Fin 4) = raw2768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix531 raw2768; decide +kernel
    rw [heq]
    exact (canonical2768 hH).trans (sound174 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node531 + (injectiveMoment H (mergeFirst pivotMatrix531 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix531 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix531 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix531 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value531, value170, value174, value180, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation532 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem sound532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node532 = Sparse.eval value532 (momentVector H) := by
  have heq : pivotMatrix532 = (fun u v => node532 (pivotPermutation532 u) v) := by apply Matrix.ext; unfold pivotMatrix532 node532 pivotPermutation532; decide +kernel
  have hmoment : injectiveMoment H node532 = injectiveMoment H pivotMatrix532 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix532 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix532 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix532 (0 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix532 (0 : Fin 4) = raw532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix532 raw532; decide +kernel
    rw [heq]
    exact (canonical532 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix532 (1 : Fin 4)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix532 (1 : Fin 4) = raw2687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix532 raw2687; decide +kernel
    rw [heq]
    exact (canonical2687 hH).trans (sound159 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix532 (2 : Fin 4)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix532 (2 : Fin 4) = raw2788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix532 raw2788; decide +kernel
    rw [heq]
    exact (canonical2788 hH).trans (sound168 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix532 (3 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix532 (3 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix532 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node532 + (injectiveMoment H (mergeFirst pivotMatrix532 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix532 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix532 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix532 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value532, value159, value168, value180, value222, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation533 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem sound533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node533 = Sparse.eval value533 (momentVector H) := by
  have heq : pivotMatrix533 = (fun u v => node533 (pivotPermutation533 u) v) := by apply Matrix.ext; unfold pivotMatrix533 node533 pivotPermutation533; decide +kernel
  have hmoment : injectiveMoment H node533 = injectiveMoment H pivotMatrix533 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix533 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix533 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix533 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix533 (0 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix533 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix533 (1 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix533 (1 : Fin 4) = raw2699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix533 raw2699; decide +kernel
    rw [heq]
    exact (canonical2699 hH).trans (sound103 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix533 (2 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix533 (2 : Fin 4) = raw2828 := by apply Matrix.ext; unfold mergeFirst pivotMatrix533 raw2828; decide +kernel
    rw [heq]
    exact (canonical2828 hH).trans (sound169 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix533 (3 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix533 (3 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix533 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node533 + (injectiveMoment H (mergeFirst pivotMatrix533 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix533 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix533 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix533 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value533, value103, value169, value184, value198, Sparse.eval] at hc ⊢
  linarith

theorem sound534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node534 = Sparse.eval value534 (momentVector H) := by
  have hc : momentVector H 487 = injectiveMoment H node534 := rfl
  simp [value534, Sparse.eval, hc]

def pivotPermutation535 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix535 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem sound535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node535 = Sparse.eval value535 (momentVector H) := by
  have heq : pivotMatrix535 = (fun u v => node535 (pivotPermutation535 u) v) := by apply Matrix.ext; unfold pivotMatrix535 node535 pivotPermutation535; decide +kernel
  have hmoment : injectiveMoment H node535 = injectiveMoment H pivotMatrix535 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix535 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix535 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix535 (0 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix535 (0 : Fin 4) = raw1353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix535 raw1353; decide +kernel
    rw [heq]
    exact (canonical1353 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix535 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix535 (1 : Fin 4) = raw2672 := by apply Matrix.ext; unfold mergeFirst pivotMatrix535 raw2672; decide +kernel
    rw [heq]
    exact (canonical2672 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix535 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix535 (2 : Fin 4) = raw2692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix535 raw2692; decide +kernel
    rw [heq]
    exact (canonical2692 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix535 (3 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix535 (3 : Fin 4) = raw2693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix535 raw2693; decide +kernel
    rw [heq]
    exact (canonical2693 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node535 + (injectiveMoment H (mergeFirst pivotMatrix535 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix535 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix535 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix535 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value535, value111, value134, value229, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation536 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix536 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

theorem sound536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node536 = Sparse.eval value536 (momentVector H) := by
  have heq : pivotMatrix536 = (fun u v => node536 (pivotPermutation536 u) v) := by apply Matrix.ext; unfold pivotMatrix536 node536 pivotPermutation536; decide +kernel
  have hmoment : injectiveMoment H node536 = injectiveMoment H pivotMatrix536 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix536 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix536 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix536 (0 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix536 (0 : Fin 4) = raw3976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix536 raw3976; decide +kernel
    rw [heq]
    exact (canonical3976 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix536 (1 : Fin 4)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix536 (1 : Fin 4) = raw2699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix536 raw2699; decide +kernel
    rw [heq]
    exact (canonical2699 hH).trans (sound103 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix536 (2 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix536 (2 : Fin 4) = raw2691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix536 raw2691; decide +kernel
    rw [heq]
    exact (canonical2691 hH).trans (sound226 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix536 (3 : Fin 4)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix536 (3 : Fin 4) = raw2687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix536 raw2687; decide +kernel
    rw [heq]
    exact (canonical2687 hH).trans (sound159 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node536 + (injectiveMoment H (mergeFirst pivotMatrix536 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix536 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix536 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix536 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value536, value103, value159, value224, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation537 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix537 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

theorem sound537 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node537 = Sparse.eval value537 (momentVector H) := by
  have heq : pivotMatrix537 = (fun u v => node537 (pivotPermutation537 u) v) := by apply Matrix.ext; unfold pivotMatrix537 node537 pivotPermutation537; decide +kernel
  have hmoment : injectiveMoment H node537 = injectiveMoment H pivotMatrix537 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix537 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix537 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix537 (0 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix537 (0 : Fin 4) = raw3979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix537 raw3979; decide +kernel
    rw [heq]
    exact (canonical3979 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix537 (1 : Fin 4)) =
      Sparse.eval value160 (momentVector H) := by
    have heq : mergeFirst pivotMatrix537 (1 : Fin 4) = raw2702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix537 raw2702; decide +kernel
    rw [heq]
    exact (canonical2702 hH).trans (sound160 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix537 (2 : Fin 4)) =
      Sparse.eval value160 (momentVector H) := by
    have heq : mergeFirst pivotMatrix537 (2 : Fin 4) = raw2694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix537 raw2694; decide +kernel
    rw [heq]
    exact (canonical2694 hH).trans (sound160 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix537 (3 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix537 (3 : Fin 4) = raw2693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix537 raw2693; decide +kernel
    rw [heq]
    exact (canonical2693 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node537 + (injectiveMoment H (mergeFirst pivotMatrix537 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix537 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix537 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix537 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value537, value111, value160, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation538 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix538 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

theorem sound538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node538 = Sparse.eval value538 (momentVector H) := by
  have heq : pivotMatrix538 = (fun u v => node538 (pivotPermutation538 u) v) := by apply Matrix.ext; unfold pivotMatrix538 node538 pivotPermutation538; decide +kernel
  have hmoment : injectiveMoment H node538 = injectiveMoment H pivotMatrix538 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix538 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix538 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix538 (0 : Fin 4)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix538 (0 : Fin 4) = raw5887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix538 raw5887; decide +kernel
    rw [heq]
    exact (canonical5887 hH).trans (sound260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix538 (1 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix538 (1 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix538 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix538 (2 : Fin 4)) =
      Sparse.eval value160 (momentVector H) := by
    have heq : mergeFirst pivotMatrix538 (2 : Fin 4) = raw2695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix538 raw2695; decide +kernel
    rw [heq]
    exact (canonical2695 hH).trans (sound160 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix538 (3 : Fin 4)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix538 (3 : Fin 4) = raw2687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix538 raw2687; decide +kernel
    rw [heq]
    exact (canonical2687 hH).trans (sound159 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node538 + (injectiveMoment H (mergeFirst pivotMatrix538 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix538 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix538 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix538 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value538, value159, value160, value180, value260, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation539 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix539 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node539 = Sparse.eval value539 (momentVector H) := by
  have heq : pivotMatrix539 = (fun u v => node539 (pivotPermutation539 u) v) := by apply Matrix.ext; unfold pivotMatrix539 node539 pivotPermutation539; decide +kernel
  have hmoment : injectiveMoment H node539 = injectiveMoment H pivotMatrix539 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix539 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix539 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix539 (0 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix539 (0 : Fin 4) = raw6754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix539 raw6754; decide +kernel
    rw [heq]
    exact (canonical6754 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix539 (1 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix539 (1 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix539 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix539 (2 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix539 (2 : Fin 4) = raw2696 := by apply Matrix.ext; unfold mergeFirst pivotMatrix539 raw2696; decide +kernel
    rw [heq]
    exact (canonical2696 hH).trans (sound111 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix539 (3 : Fin 4)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix539 (3 : Fin 4) = raw2687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix539 raw2687; decide +kernel
    rw [heq]
    exact (canonical2687 hH).trans (sound159 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node539 + (injectiveMoment H (mergeFirst pivotMatrix539 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix539 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix539 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix539 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value539, value111, value159, value184, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation540 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix540 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![1, 0, -1]]

theorem sound540 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node540 = Sparse.eval value540 (momentVector H) := by
  have heq : pivotMatrix540 = (fun u v => node540 (pivotPermutation540 u) v) := by apply Matrix.ext; unfold pivotMatrix540 node540 pivotPermutation540; decide +kernel
  have hmoment : injectiveMoment H node540 = injectiveMoment H pivotMatrix540 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix540 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix540 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix540 (0 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix540 (0 : Fin 4) = raw5907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix540 raw5907; decide +kernel
    rw [heq]
    exact (canonical5907 hH).trans (sound247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix540 (1 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix540 (1 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix540 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix540 (2 : Fin 4)) =
      Sparse.eval value158 (momentVector H) := by
    have heq : mergeFirst pivotMatrix540 (2 : Fin 4) = raw2707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix540 raw2707; decide +kernel
    rw [heq]
    exact (canonical2707 hH).trans (sound158 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix540 (3 : Fin 4)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix540 (3 : Fin 4) = raw2704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix540 raw2704; decide +kernel
    rw [heq]
    exact (canonical2704 hH).trans (sound161 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node540 + (injectiveMoment H (mergeFirst pivotMatrix540 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix540 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix540 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix540 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value540, value158, value161, value187, value247, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation541 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix541 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 1, -3]]

theorem sound541 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node541 = Sparse.eval value541 (momentVector H) := by
  have heq : pivotMatrix541 = (fun u v => node541 (pivotPermutation541 u) v) := by apply Matrix.ext; unfold pivotMatrix541 node541 pivotPermutation541; decide +kernel
  have hmoment : injectiveMoment H node541 = injectiveMoment H pivotMatrix541 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix541 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix541 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix541 (0 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix541 (0 : Fin 4) = raw4029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix541 raw4029; decide +kernel
    rw [heq]
    exact (canonical4029 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix541 (1 : Fin 4)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix541 (1 : Fin 4) = raw2750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix541 raw2750; decide +kernel
    rw [heq]
    exact (canonical2750 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix541 (2 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix541 (2 : Fin 4) = raw2718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix541 raw2718; decide +kernel
    rw [heq]
    exact (canonical2718 hH).trans (sound162 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix541 (3 : Fin 4)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix541 (3 : Fin 4) = raw2714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix541 raw2714; decide +kernel
    rw [heq]
    exact (canonical2714 hH).trans (sound140 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node541 + (injectiveMoment H (mergeFirst pivotMatrix541 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix541 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix541 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix541 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value541, value140, value162, value168, value169, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation542 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix542 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem sound542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node542 = Sparse.eval value542 (momentVector H) := by
  have heq : pivotMatrix542 = (fun u v => node542 (pivotPermutation542 u) v) := by apply Matrix.ext; unfold pivotMatrix542 node542 pivotPermutation542; decide +kernel
  have hmoment : injectiveMoment H node542 = injectiveMoment H pivotMatrix542 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix542 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix542 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix542 (0 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix542 (0 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix542 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix542 (1 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix542 (1 : Fin 4) = raw2756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix542 raw2756; decide +kernel
    rw [heq]
    exact (canonical2756 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix542 (2 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix542 (2 : Fin 4) = raw2721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix542 raw2721; decide +kernel
    rw [heq]
    exact (canonical2721 hH).trans (sound163 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix542 (3 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix542 (3 : Fin 4) = raw2718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix542 raw2718; decide +kernel
    rw [heq]
    exact (canonical2718 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node542 + (injectiveMoment H (mergeFirst pivotMatrix542 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix542 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix542 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix542 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value542, value162, value163, value169, value197, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation543 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix543 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem sound543 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node543 = Sparse.eval value543 (momentVector H) := by
  have heq : pivotMatrix543 = (fun u v => node543 (pivotPermutation543 u) v) := by apply Matrix.ext; unfold pivotMatrix543 node543 pivotPermutation543; decide +kernel
  have hmoment : injectiveMoment H node543 = injectiveMoment H pivotMatrix543 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix543 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix543 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix543 (0 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix543 (0 : Fin 4) = raw4042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix543 raw4042; decide +kernel
    rw [heq]
    exact (canonical4042 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix543 (1 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix543 (1 : Fin 4) = raw2765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix543 raw2765; decide +kernel
    rw [heq]
    exact (canonical2765 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix543 (2 : Fin 4)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix543 (2 : Fin 4) = raw2725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix543 raw2725; decide +kernel
    rw [heq]
    exact (canonical2725 hH).trans (sound166 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix543 (3 : Fin 4)) =
      Sparse.eval value165 (momentVector H) := by
    have heq : mergeFirst pivotMatrix543 (3 : Fin 4) = raw2724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix543 raw2724; decide +kernel
    rw [heq]
    exact (canonical2724 hH).trans (sound165 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node543 + (injectiveMoment H (mergeFirst pivotMatrix543 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix543 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix543 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix543 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value543, value165, value166, value173, value201, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation544 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix544 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

theorem sound544 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node544 = Sparse.eval value544 (momentVector H) := by
  have heq : pivotMatrix544 = (fun u v => node544 (pivotPermutation544 u) v) := by apply Matrix.ext; unfold pivotMatrix544 node544 pivotPermutation544; decide +kernel
  have hmoment : injectiveMoment H node544 = injectiveMoment H pivotMatrix544 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix544 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix544 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix544 (0 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix544 (0 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix544 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix544 (1 : Fin 4)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix544 (1 : Fin 4) = raw2766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix544 raw2766; decide +kernel
    rw [heq]
    exact (canonical2766 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix544 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix544 (2 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix544 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix544 (3 : Fin 4)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix544 (3 : Fin 4) = raw2725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix544 raw2725; decide +kernel
    rw [heq]
    exact (canonical2725 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node544 + (injectiveMoment H (mergeFirst pivotMatrix544 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix544 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix544 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix544 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value544, value166, value167, value169, value174, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation545 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix545 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem sound545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node545 = Sparse.eval value545 (momentVector H) := by
  have heq : pivotMatrix545 = (fun u v => node545 (pivotPermutation545 u) v) := by apply Matrix.ext; unfold pivotMatrix545 node545 pivotPermutation545; decide +kernel
  have hmoment : injectiveMoment H node545 = injectiveMoment H pivotMatrix545 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix545 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix545 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix545 (0 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (0 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix545 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (1 : Fin 4) = raw2767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2767; decide +kernel
    rw [heq]
    exact (canonical2767 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix545 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (2 : Fin 4) = raw2727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2727; decide +kernel
    rw [heq]
    exact (canonical2727 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix545 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (3 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node545 + (injectiveMoment H (mergeFirst pivotMatrix545 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value545, value167, value175, value202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation546 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix546 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

theorem sound546 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node546 = Sparse.eval value546 (momentVector H) := by
  have heq : pivotMatrix546 = (fun u v => node546 (pivotPermutation546 u) v) := by apply Matrix.ext; unfold pivotMatrix546 node546 pivotPermutation546; decide +kernel
  have hmoment : injectiveMoment H node546 = injectiveMoment H pivotMatrix546 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix546 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix546 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix546 (0 : Fin 4)) =
      Sparse.eval value264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix546 (0 : Fin 4) = raw5913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix546 raw5913; decide +kernel
    rw [heq]
    exact (canonical5913 hH).trans (sound264 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix546 (1 : Fin 4)) =
      Sparse.eval value183 (momentVector H) := by
    have heq : mergeFirst pivotMatrix546 (1 : Fin 4) = raw2854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix546 raw2854; decide +kernel
    rw [heq]
    exact (canonical2854 hH).trans (sound183 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix546 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix546 (2 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix546 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix546 (3 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix546 (3 : Fin 4) = raw2718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix546 raw2718; decide +kernel
    rw [heq]
    exact (canonical2718 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node546 + (injectiveMoment H (mergeFirst pivotMatrix546 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix546 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix546 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix546 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value546, value162, value167, value183, value264, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation547 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix547 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem sound547 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node547 = Sparse.eval value547 (momentVector H) := by
  have heq : pivotMatrix547 = (fun u v => node547 (pivotPermutation547 u) v) := by apply Matrix.ext; unfold pivotMatrix547 node547 pivotPermutation547; decide +kernel
  have hmoment : injectiveMoment H node547 = injectiveMoment H pivotMatrix547 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix547 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix547 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix547 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix547 (0 : Fin 4) = raw6783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix547 raw6783; decide +kernel
    rw [heq]
    exact (canonical6783 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix547 (1 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix547 (1 : Fin 4) = raw2858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix547 raw2858; decide +kernel
    rw [heq]
    exact (canonical2858 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix547 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix547 (2 : Fin 4) = raw2727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix547 raw2727; decide +kernel
    rw [heq]
    exact (canonical2727 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix547 (3 : Fin 4)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix547 (3 : Fin 4) = raw2718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix547 raw2718; decide +kernel
    rw [heq]
    exact (canonical2718 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node547 + (injectiveMoment H (mergeFirst pivotMatrix547 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix547 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix547 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix547 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value547, value162, value167, value184, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation548 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix548 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem sound548 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node548 = Sparse.eval value548 (momentVector H) := by
  have heq : pivotMatrix548 = (fun u v => node548 (pivotPermutation548 u) v) := by apply Matrix.ext; unfold pivotMatrix548 node548 pivotPermutation548; decide +kernel
  have hmoment : injectiveMoment H node548 = injectiveMoment H pivotMatrix548 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix548 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix548 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix548 (0 : Fin 4)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix548 (0 : Fin 4) = raw5914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix548 raw5914; decide +kernel
    rw [heq]
    exact (canonical5914 hH).trans (sound265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix548 (1 : Fin 4)) =
      Sparse.eval value186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix548 (1 : Fin 4) = raw2855 := by apply Matrix.ext; unfold mergeFirst pivotMatrix548 raw2855; decide +kernel
    rw [heq]
    exact (canonical2855 hH).trans (sound186 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix548 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix548 (2 : Fin 4) = raw2727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix548 raw2727; decide +kernel
    rw [heq]
    exact (canonical2727 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix548 (3 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix548 (3 : Fin 4) = raw2721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix548 raw2721; decide +kernel
    rw [heq]
    exact (canonical2721 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node548 + (injectiveMoment H (mergeFirst pivotMatrix548 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix548 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix548 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix548 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value548, value163, value167, value186, value265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation549 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix549 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem sound549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node549 = Sparse.eval value549 (momentVector H) := by
  have heq : pivotMatrix549 = (fun u v => node549 (pivotPermutation549 u) v) := by apply Matrix.ext; unfold pivotMatrix549 node549 pivotPermutation549; decide +kernel
  have hmoment : injectiveMoment H node549 = injectiveMoment H pivotMatrix549 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix549 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix549 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix549 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix549 (0 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix549 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix549 (1 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix549 (1 : Fin 4) = raw2859 := by apply Matrix.ext; unfold mergeFirst pivotMatrix549 raw2859; decide +kernel
    rw [heq]
    exact (canonical2859 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix549 (2 : Fin 4)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix549 (2 : Fin 4) = raw2728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix549 raw2728; decide +kernel
    rw [heq]
    exact (canonical2728 hH).trans (sound166 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix549 (3 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix549 (3 : Fin 4) = raw2721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix549 raw2721; decide +kernel
    rw [heq]
    exact (canonical2721 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node549 + (injectiveMoment H (mergeFirst pivotMatrix549 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix549 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix549 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix549 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value549, value163, value166, value187, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation550 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix550 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

theorem sound550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node550 = Sparse.eval value550 (momentVector H) := by
  have heq : pivotMatrix550 = (fun u v => node550 (pivotPermutation550 u) v) := by apply Matrix.ext; unfold pivotMatrix550 node550 pivotPermutation550; decide +kernel
  have hmoment : injectiveMoment H node550 = injectiveMoment H pivotMatrix550 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix550 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix550 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix550 (0 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix550 (0 : Fin 4) = raw5915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix550 raw5915; decide +kernel
    rw [heq]
    exact (canonical5915 hH).trans (sound266 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix550 (1 : Fin 4)) =
      Sparse.eval value189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix550 (1 : Fin 4) = raw2856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix550 raw2856; decide +kernel
    rw [heq]
    exact (canonical2856 hH).trans (sound189 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix550 (2 : Fin 4)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix550 (2 : Fin 4) = raw2728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix550 raw2728; decide +kernel
    rw [heq]
    exact (canonical2728 hH).trans (sound166 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix550 (3 : Fin 4)) =
      Sparse.eval value164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix550 (3 : Fin 4) = raw2723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix550 raw2723; decide +kernel
    rw [heq]
    exact (canonical2723 hH).trans (sound164 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node550 + (injectiveMoment H (mergeFirst pivotMatrix550 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix550 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix550 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix550 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value550, value164, value166, value189, value266, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation551 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix551 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem sound551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node551 = Sparse.eval value551 (momentVector H) := by
  have heq : pivotMatrix551 = (fun u v => node551 (pivotPermutation551 u) v) := by apply Matrix.ext; unfold pivotMatrix551 node551 pivotPermutation551; decide +kernel
  have hmoment : injectiveMoment H node551 = injectiveMoment H pivotMatrix551 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix551 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix551 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix551 (0 : Fin 4)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix551 (0 : Fin 4) = raw1374 := by apply Matrix.ext; unfold mergeFirst pivotMatrix551 raw1374; decide +kernel
    rw [heq]
    exact (canonical1374 hH).trans (sound141 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix551 (1 : Fin 4)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix551 (1 : Fin 4) = raw2721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix551 raw2721; decide +kernel
    rw [heq]
    exact (canonical2721 hH).trans (sound163 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix551 (2 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix551 (2 : Fin 4) = raw2756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix551 raw2756; decide +kernel
    rw [heq]
    exact (canonical2756 hH).trans (sound169 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix551 (3 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix551 (3 : Fin 4) = raw2759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix551 raw2759; decide +kernel
    rw [heq]
    exact (canonical2759 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node551 + (injectiveMoment H (mergeFirst pivotMatrix551 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix551 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix551 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix551 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value551, value141, value163, value169, value170, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation552 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix552 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem sound552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node552 = Sparse.eval value552 (momentVector H) := by
  have heq : pivotMatrix552 = (fun u v => node552 (pivotPermutation552 u) v) := by apply Matrix.ext; unfold pivotMatrix552 node552 pivotPermutation552; decide +kernel
  have hmoment : injectiveMoment H node552 = injectiveMoment H pivotMatrix552 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix552 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix552 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix552 (0 : Fin 4)) =
      Sparse.eval value142 (momentVector H) := by
    have heq : mergeFirst pivotMatrix552 (0 : Fin 4) = raw1376 := by apply Matrix.ext; unfold mergeFirst pivotMatrix552 raw1376; decide +kernel
    rw [heq]
    exact (canonical1376 hH).trans (sound142 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix552 (1 : Fin 4)) =
      Sparse.eval value165 (momentVector H) := by
    have heq : mergeFirst pivotMatrix552 (1 : Fin 4) = raw2724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix552 raw2724; decide +kernel
    rw [heq]
    exact (canonical2724 hH).trans (sound165 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix552 (2 : Fin 4)) =
      Sparse.eval value172 (momentVector H) := by
    have heq : mergeFirst pivotMatrix552 (2 : Fin 4) = raw2762 := by apply Matrix.ext; unfold mergeFirst pivotMatrix552 raw2762; decide +kernel
    rw [heq]
    exact (canonical2762 hH).trans (sound172 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix552 (3 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix552 (3 : Fin 4) = raw2765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix552 raw2765; decide +kernel
    rw [heq]
    exact (canonical2765 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node552 + (injectiveMoment H (mergeFirst pivotMatrix552 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix552 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix552 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix552 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value552, value142, value165, value172, value173, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation553 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix553 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem sound553 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node553 = Sparse.eval value553 (momentVector H) := by
  have heq : pivotMatrix553 = (fun u v => node553 (pivotPermutation553 u) v) := by apply Matrix.ext; unfold pivotMatrix553 node553 pivotPermutation553; decide +kernel
  have hmoment : injectiveMoment H node553 = injectiveMoment H pivotMatrix553 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix553 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix553 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix553 (0 : Fin 4)) =
      Sparse.eval value143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix553 (0 : Fin 4) = raw1377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix553 raw1377; decide +kernel
    rw [heq]
    exact (canonical1377 hH).trans (sound143 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix553 (1 : Fin 4)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix553 (1 : Fin 4) = raw2725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix553 raw2725; decide +kernel
    rw [heq]
    exact (canonical2725 hH).trans (sound166 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix553 (2 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix553 (2 : Fin 4) = raw2765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix553 raw2765; decide +kernel
    rw [heq]
    exact (canonical2765 hH).trans (sound173 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix553 (3 : Fin 4)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix553 (3 : Fin 4) = raw2766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix553 raw2766; decide +kernel
    rw [heq]
    exact (canonical2766 hH).trans (sound174 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node553 + (injectiveMoment H (mergeFirst pivotMatrix553 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix553 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix553 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix553 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value553, value143, value166, value173, value174, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation554 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix554 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem sound554 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node554 = Sparse.eval value554 (momentVector H) := by
  have heq : pivotMatrix554 = (fun u v => node554 (pivotPermutation554 u) v) := by apply Matrix.ext; unfold pivotMatrix554 node554 pivotPermutation554; decide +kernel
  have hmoment : injectiveMoment H node554 = injectiveMoment H pivotMatrix554 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix554 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix554 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix554 (0 : Fin 4)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix554 (0 : Fin 4) = raw1378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix554 raw1378; decide +kernel
    rw [heq]
    exact (canonical1378 hH).trans (sound144 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix554 (1 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix554 (1 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix554 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix554 (2 : Fin 4)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix554 (2 : Fin 4) = raw2766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix554 raw2766; decide +kernel
    rw [heq]
    exact (canonical2766 hH).trans (sound174 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix554 (3 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix554 (3 : Fin 4) = raw2767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix554 raw2767; decide +kernel
    rw [heq]
    exact (canonical2767 hH).trans (sound175 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node554 + (injectiveMoment H (mergeFirst pivotMatrix554 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix554 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix554 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix554 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value554, value144, value167, value174, value175, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation555 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix555 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem sound555 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node555 = Sparse.eval value555 (momentVector H) := by
  have heq : pivotMatrix555 = (fun u v => node555 (pivotPermutation555 u) v) := by apply Matrix.ext; unfold pivotMatrix555 node555 pivotPermutation555; decide +kernel
  have hmoment : injectiveMoment H node555 = injectiveMoment H pivotMatrix555 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix555 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix555 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix555 (0 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix555 (0 : Fin 4) = raw1403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix555 raw1403; decide +kernel
    rw [heq]
    exact (canonical1403 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix555 (1 : Fin 4)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix555 (1 : Fin 4) = raw2774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix555 raw2774; decide +kernel
    rw [heq]
    exact (canonical2774 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix555 (2 : Fin 4)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix555 (2 : Fin 4) = raw2794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix555 raw2794; decide +kernel
    rw [heq]
    exact (canonical2794 hH).trans (sound57 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix555 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix555 (3 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix555 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node555 + (injectiveMoment H (mergeFirst pivotMatrix555 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix555 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix555 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix555 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value555, value145, value176, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation556 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix556 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem sound556 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node556 = Sparse.eval value556 (momentVector H) := by
  have heq : pivotMatrix556 = (fun u v => node556 (pivotPermutation556 u) v) := by apply Matrix.ext; unfold pivotMatrix556 node556 pivotPermutation556; decide +kernel
  have hmoment : injectiveMoment H node556 = injectiveMoment H pivotMatrix556 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix556 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix556 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix556 (0 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix556 (0 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix556 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix556 (1 : Fin 4)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix556 (1 : Fin 4) = raw2776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix556 raw2776; decide +kernel
    rw [heq]
    exact (canonical2776 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix556 (2 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix556 (2 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix556 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix556 (3 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix556 (3 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix556 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node556 + (injectiveMoment H (mergeFirst pivotMatrix556 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix556 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix556 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix556 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value556, value146, value176, value177, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation557 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem sound557 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node557 = Sparse.eval value557 (momentVector H) := by
  have heq : pivotMatrix557 = (fun u v => node557 (pivotPermutation557 u) v) := by apply Matrix.ext; unfold pivotMatrix557 node557 pivotPermutation557; decide +kernel
  have hmoment : injectiveMoment H node557 = injectiveMoment H pivotMatrix557 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix557 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix557 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix557 (0 : Fin 4)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix557 (0 : Fin 4) = raw1412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix557 raw1412; decide +kernel
    rw [heq]
    exact (canonical1412 hH).trans (sound147 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix557 (1 : Fin 4)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix557 (1 : Fin 4) = raw2779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix557 raw2779; decide +kernel
    rw [heq]
    exact (canonical2779 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix557 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix557 (2 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix557 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix557 (3 : Fin 4)) =
      Sparse.eval value178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix557 (3 : Fin 4) = raw2815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix557 raw2815; decide +kernel
    rw [heq]
    exact (canonical2815 hH).trans (sound178 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node557 + (injectiveMoment H (mergeFirst pivotMatrix557 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix557 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix557 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix557 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value557, value147, value177, value178, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation558 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

theorem sound558 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node558 = Sparse.eval value558 (momentVector H) := by
  have heq : pivotMatrix558 = (fun u v => node558 (pivotPermutation558 u) v) := by apply Matrix.ext; unfold pivotMatrix558 node558 pivotPermutation558; decide +kernel
  have hmoment : injectiveMoment H node558 = injectiveMoment H pivotMatrix558 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix558 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix558 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix558 (0 : Fin 4)) =
      Sparse.eval value148 (momentVector H) := by
    have heq : mergeFirst pivotMatrix558 (0 : Fin 4) = raw1413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix558 raw1413; decide +kernel
    rw [heq]
    exact (canonical1413 hH).trans (sound148 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix558 (1 : Fin 4)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix558 (1 : Fin 4) = raw2780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix558 raw2780; decide +kernel
    rw [heq]
    exact (canonical2780 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix558 (2 : Fin 4)) =
      Sparse.eval value179 (momentVector H) := by
    have heq : mergeFirst pivotMatrix558 (2 : Fin 4) = raw2816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix558 raw2816; decide +kernel
    rw [heq]
    exact (canonical2816 hH).trans (sound179 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix558 (3 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix558 (3 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix558 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node558 + (injectiveMoment H (mergeFirst pivotMatrix558 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix558 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix558 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix558 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value558, value148, value179, value180, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation559 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix559 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node559 = Sparse.eval value559 (momentVector H) := by
  have heq : pivotMatrix559 = (fun u v => node559 (pivotPermutation559 u) v) := by apply Matrix.ext; unfold pivotMatrix559 node559 pivotPermutation559; decide +kernel
  have hmoment : injectiveMoment H node559 = injectiveMoment H pivotMatrix559 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix559 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix559 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix559 (0 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (0 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix559 (1 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (1 : Fin 4) = raw2781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw2781; decide +kernel
    rw [heq]
    exact (canonical2781 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix559 (2 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (2 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix559 (3 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix559 (3 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix559 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node559 + (injectiveMoment H (mergeFirst pivotMatrix559 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix559 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix559 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix559 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value559, value149, value180, value181, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation560 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix560 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound560 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node560 = Sparse.eval value560 (momentVector H) := by
  have heq : pivotMatrix560 = (fun u v => node560 (pivotPermutation560 u) v) := by apply Matrix.ext; unfold pivotMatrix560 node560 pivotPermutation560; decide +kernel
  have hmoment : injectiveMoment H node560 = injectiveMoment H pivotMatrix560 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix560 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix560 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix560 (0 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix560 (0 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix560 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix560 (1 : Fin 4)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix560 (1 : Fin 4) = raw2782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix560 raw2782; decide +kernel
    rw [heq]
    exact (canonical2782 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix560 (2 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix560 (2 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix560 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix560 (3 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix560 (3 : Fin 4) = raw2821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix560 raw2821; decide +kernel
    rw [heq]
    exact (canonical2821 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node560 + (injectiveMoment H (mergeFirst pivotMatrix560 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix560 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix560 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix560 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value560, value150, value181, value271, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation561 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix561 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node561 = Sparse.eval value561 (momentVector H) := by
  have heq : pivotMatrix561 = (fun u v => node561 (pivotPermutation561 u) v) := by apply Matrix.ext; unfold pivotMatrix561 node561 pivotPermutation561; decide +kernel
  have hmoment : injectiveMoment H node561 = injectiveMoment H pivotMatrix561 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix561 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix561 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix561 (0 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix561 (0 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix561 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix561 (1 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix561 (1 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix561 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix561 (2 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix561 (2 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix561 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix561 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix561 (3 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix561 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node561 + (injectiveMoment H (mergeFirst pivotMatrix561 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix561 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix561 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix561 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value561, value153, value181, value184, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation562 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix562 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound562 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node562 = Sparse.eval value562 (momentVector H) := by
  have heq : pivotMatrix562 = (fun u v => node562 (pivotPermutation562 u) v) := by apply Matrix.ext; unfold pivotMatrix562 node562 pivotPermutation562; decide +kernel
  have hmoment : injectiveMoment H node562 = injectiveMoment H pivotMatrix562 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix562 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix562 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix562 (0 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix562 (0 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix562 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix562 (1 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix562 (1 : Fin 4) = raw2821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix562 raw2821; decide +kernel
    rw [heq]
    exact (canonical2821 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix562 (2 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix562 (2 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix562 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix562 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix562 (3 : Fin 4) = raw2843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix562 raw2843; decide +kernel
    rw [heq]
    exact (canonical2843 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node562 + (injectiveMoment H (mergeFirst pivotMatrix562 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix562 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix562 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix562 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value562, value145, value185, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation563 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix563 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound563 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node563 = Sparse.eval value563 (momentVector H) := by
  have heq : pivotMatrix563 = (fun u v => node563 (pivotPermutation563 u) v) := by apply Matrix.ext; unfold pivotMatrix563 node563 pivotPermutation563; decide +kernel
  have hmoment : injectiveMoment H node563 = injectiveMoment H pivotMatrix563 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix563 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix563 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix563 (0 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix563 (0 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix563 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix563 (1 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix563 (1 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix563 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix563 (2 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix563 (2 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix563 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix563 (3 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix563 (3 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix563 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node563 + (injectiveMoment H (mergeFirst pivotMatrix563 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix563 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix563 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix563 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value563, value155, value185, value187, value188, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation564 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix564 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem sound564 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node564 = Sparse.eval value564 (momentVector H) := by
  have heq : pivotMatrix564 = (fun u v => node564 (pivotPermutation564 u) v) := by apply Matrix.ext; unfold pivotMatrix564 node564 pivotPermutation564; decide +kernel
  have hmoment : injectiveMoment H node564 = injectiveMoment H pivotMatrix564 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix564 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix564 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix564 (0 : Fin 4)) =
      Sparse.eval value156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix564 (0 : Fin 4) = raw1440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix564 raw1440; decide +kernel
    rw [heq]
    exact (canonical1440 hH).trans (sound156 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix564 (1 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix564 (1 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix564 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix564 (2 : Fin 4)) =
      Sparse.eval value189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix564 (2 : Fin 4) = raw2850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix564 raw2850; decide +kernel
    rw [heq]
    exact (canonical2850 hH).trans (sound189 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix564 (3 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix564 (3 : Fin 4) = raw2851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix564 raw2851; decide +kernel
    rw [heq]
    exact (canonical2851 hH).trans (sound190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node564 + (injectiveMoment H (mergeFirst pivotMatrix564 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix564 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix564 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix564 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value564, value156, value187, value189, value190, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation565 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix565 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem sound565 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node565 = Sparse.eval value565 (momentVector H) := by
  have heq : pivotMatrix565 = (fun u v => node565 (pivotPermutation565 u) v) := by apply Matrix.ext; unfold pivotMatrix565 node565 pivotPermutation565; decide +kernel
  have hmoment : injectiveMoment H node565 = injectiveMoment H pivotMatrix565 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix565 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix565 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix565 (0 : Fin 4)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix565 (0 : Fin 4) = raw1441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix565 raw1441; decide +kernel
    rw [heq]
    exact (canonical1441 hH).trans (sound157 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix565 (1 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix565 (1 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix565 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix565 (2 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix565 (2 : Fin 4) = raw2851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix565 raw2851; decide +kernel
    rw [heq]
    exact (canonical2851 hH).trans (sound190 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix565 (3 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix565 (3 : Fin 4) = raw2852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix565 raw2852; decide +kernel
    rw [heq]
    exact (canonical2852 hH).trans (sound190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node565 + (injectiveMoment H (mergeFirst pivotMatrix565 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix565 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix565 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix565 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value565, value157, value188, value190, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation566 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix566 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem sound566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node566 = Sparse.eval value566 (momentVector H) := by
  have heq : pivotMatrix566 = (fun u v => node566 (pivotPermutation566 u) v) := by apply Matrix.ext; unfold pivotMatrix566 node566 pivotPermutation566; decide +kernel
  have hmoment : injectiveMoment H node566 = injectiveMoment H pivotMatrix566 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix566 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix566 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix566 (0 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (0 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix566 (1 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (1 : Fin 4) = raw2833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2833; decide +kernel
    rw [heq]
    exact (canonical2833 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix566 (2 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (2 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix566 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix566 (3 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix566 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node566 + (injectiveMoment H (mergeFirst pivotMatrix566 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix566 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value566, value176, value177, value207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation567 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix567 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

theorem sound567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node567 = Sparse.eval value567 (momentVector H) := by
  have heq : pivotMatrix567 = (fun u v => node567 (pivotPermutation567 u) v) := by apply Matrix.ext; unfold pivotMatrix567 node567 pivotPermutation567; decide +kernel
  have hmoment : injectiveMoment H node567 = injectiveMoment H pivotMatrix567 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix567 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix567 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix567 (0 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix567 (0 : Fin 4) = raw4123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix567 raw4123; decide +kernel
    rw [heq]
    exact (canonical4123 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix567 (1 : Fin 4)) =
      Sparse.eval value182 (momentVector H) := by
    have heq : mergeFirst pivotMatrix567 (1 : Fin 4) = raw2834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix567 raw2834; decide +kernel
    rw [heq]
    exact (canonical2834 hH).trans (sound182 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix567 (2 : Fin 4)) =
      Sparse.eval value178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix567 (2 : Fin 4) = raw2815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix567 raw2815; decide +kernel
    rw [heq]
    exact (canonical2815 hH).trans (sound178 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix567 (3 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix567 (3 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix567 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node567 + (injectiveMoment H (mergeFirst pivotMatrix567 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix567 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix567 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix567 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value567, value177, value178, value182, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation568 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem sound568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node568 = Sparse.eval value568 (momentVector H) := by
  have heq : pivotMatrix568 = (fun u v => node568 (pivotPermutation568 u) v) := by apply Matrix.ext; unfold pivotMatrix568 node568 pivotPermutation568; decide +kernel
  have hmoment : injectiveMoment H node568 = injectiveMoment H pivotMatrix568 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix568 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix568 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix568 (0 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix568 (0 : Fin 4) = raw4127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix568 raw4127; decide +kernel
    rw [heq]
    exact (canonical4127 hH).trans (sound209 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix568 (1 : Fin 4)) =
      Sparse.eval value183 (momentVector H) := by
    have heq : mergeFirst pivotMatrix568 (1 : Fin 4) = raw2835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix568 raw2835; decide +kernel
    rw [heq]
    exact (canonical2835 hH).trans (sound183 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix568 (2 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix568 (2 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix568 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix568 (3 : Fin 4)) =
      Sparse.eval value179 (momentVector H) := by
    have heq : mergeFirst pivotMatrix568 (3 : Fin 4) = raw2816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix568 raw2816; decide +kernel
    rw [heq]
    exact (canonical2816 hH).trans (sound179 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node568 + (injectiveMoment H (mergeFirst pivotMatrix568 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix568 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix568 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix568 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value568, value179, value180, value183, value209, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation569 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix569 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound569 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node569 = Sparse.eval value569 (momentVector H) := by
  have heq : pivotMatrix569 = (fun u v => node569 (pivotPermutation569 u) v) := by apply Matrix.ext; unfold pivotMatrix569 node569 pivotPermutation569; decide +kernel
  have hmoment : injectiveMoment H node569 = injectiveMoment H pivotMatrix569 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix569 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix569 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix569 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (0 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix569 (1 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (1 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix569 (2 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (2 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix569 (3 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix569 (3 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix569 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node569 + (injectiveMoment H (mergeFirst pivotMatrix569 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix569 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix569 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix569 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value569, value180, value181, value184, value210, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation570 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix570 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound570 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node570 = Sparse.eval value570 (momentVector H) := by
  have heq : pivotMatrix570 = (fun u v => node570 (pivotPermutation570 u) v) := by apply Matrix.ext; unfold pivotMatrix570 node570 pivotPermutation570; decide +kernel
  have hmoment : injectiveMoment H node570 = injectiveMoment H pivotMatrix570 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix570 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix570 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix570 (0 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix570 (0 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix570 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix570 (1 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix570 (1 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix570 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix570 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix570 (2 : Fin 4) = raw2821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix570 raw2821; decide +kernel
    rw [heq]
    exact (canonical2821 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix570 (3 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix570 (3 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix570 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node570 + (injectiveMoment H (mergeFirst pivotMatrix570 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix570 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix570 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix570 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value570, value181, value185, value271, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation571 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix571 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem sound571 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node571 = Sparse.eval value571 (momentVector H) := by
  have heq : pivotMatrix571 = (fun u v => node571 (pivotPermutation571 u) v) := by apply Matrix.ext; unfold pivotMatrix571 node571 pivotPermutation571; decide +kernel
  have hmoment : injectiveMoment H node571 = injectiveMoment H pivotMatrix571 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix571 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix571 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix571 (0 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix571 (0 : Fin 4) = raw4138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix571 raw4138; decide +kernel
    rw [heq]
    exact (canonical4138 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix571 (1 : Fin 4)) =
      Sparse.eval value186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix571 (1 : Fin 4) = raw2846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix571 raw2846; decide +kernel
    rw [heq]
    exact (canonical2846 hH).trans (sound186 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix571 (2 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix571 (2 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix571 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix571 (3 : Fin 4)) =
      Sparse.eval value183 (momentVector H) := by
    have heq : mergeFirst pivotMatrix571 (3 : Fin 4) = raw2835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix571 raw2835; decide +kernel
    rw [heq]
    exact (canonical2835 hH).trans (sound183 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node571 + (injectiveMoment H (mergeFirst pivotMatrix571 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix571 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix571 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix571 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value571, value183, value184, value186, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation572 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix572 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem sound572 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node572 = Sparse.eval value572 (momentVector H) := by
  have heq : pivotMatrix572 = (fun u v => node572 (pivotPermutation572 u) v) := by apply Matrix.ext; unfold pivotMatrix572 node572 pivotPermutation572; decide +kernel
  have hmoment : injectiveMoment H node572 = injectiveMoment H pivotMatrix572 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix572 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix572 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix572 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix572 (0 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix572 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix572 (1 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix572 (1 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix572 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix572 (2 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix572 (2 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix572 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix572 (3 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix572 (3 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix572 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node572 + (injectiveMoment H (mergeFirst pivotMatrix572 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix572 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix572 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix572 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value572, value184, value185, value187, value203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation573 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem sound573 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node573 = Sparse.eval value573 (momentVector H) := by
  have heq : pivotMatrix573 = (fun u v => node573 (pivotPermutation573 u) v) := by apply Matrix.ext; unfold pivotMatrix573 node573 pivotPermutation573; decide +kernel
  have hmoment : injectiveMoment H node573 = injectiveMoment H pivotMatrix573 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix573 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix573 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix573 (0 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (0 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix573 (1 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (1 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix573 (2 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (2 : Fin 4) = raw2843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2843; decide +kernel
    rw [heq]
    exact (canonical2843 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix573 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix573 (3 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix573 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node573 + (injectiveMoment H (mergeFirst pivotMatrix573 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix573 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value573, value185, value188, value207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation574 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem sound574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node574 = Sparse.eval value574 (momentVector H) := by
  have heq : pivotMatrix574 = (fun u v => node574 (pivotPermutation574 u) v) := by apply Matrix.ext; unfold pivotMatrix574 node574 pivotPermutation574; decide +kernel
  have hmoment : injectiveMoment H node574 = injectiveMoment H pivotMatrix574 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix574 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix574 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix574 (0 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix574 (0 : Fin 4) = raw4144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix574 raw4144; decide +kernel
    rw [heq]
    exact (canonical4144 hH).trans (sound214 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix574 (1 : Fin 4)) =
      Sparse.eval value189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix574 (1 : Fin 4) = raw2850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix574 raw2850; decide +kernel
    rw [heq]
    exact (canonical2850 hH).trans (sound189 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix574 (2 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix574 (2 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix574 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix574 (3 : Fin 4)) =
      Sparse.eval value186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix574 (3 : Fin 4) = raw2846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix574 raw2846; decide +kernel
    rw [heq]
    exact (canonical2846 hH).trans (sound186 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node574 + (injectiveMoment H (mergeFirst pivotMatrix574 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix574 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix574 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix574 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value574, value186, value187, value189, value214, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation575 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix575 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem sound575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node575 = Sparse.eval value575 (momentVector H) := by
  have heq : pivotMatrix575 = (fun u v => node575 (pivotPermutation575 u) v) := by apply Matrix.ext; unfold pivotMatrix575 node575 pivotPermutation575; decide +kernel
  have hmoment : injectiveMoment H node575 = injectiveMoment H pivotMatrix575 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix575 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix575 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix575 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (0 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix575 (1 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (1 : Fin 4) = raw2851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw2851; decide +kernel
    rw [heq]
    exact (canonical2851 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix575 (2 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (2 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix575 (3 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix575 (3 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix575 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node575 + (injectiveMoment H (mergeFirst pivotMatrix575 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix575 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix575 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix575 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value575, value187, value188, value190, value215, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
