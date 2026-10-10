import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation64 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix64 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

theorem sound64 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node64 = Sparse.eval value64 (momentVector H) := by
  have heq : pivotMatrix64 = (fun u v => node64 (pivotPermutation64 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node64 = injectiveMoment H pivotMatrix64 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix64 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix64 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (0 : Fin 2) = raw7895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7895 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (1 : Fin 2) = raw10000 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical10000 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node64 + (injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value64, value5, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation65 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix65 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation66 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix66 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![1, -1], ![1, -1], ![2, -2]]

theorem sound66 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node66 = Sparse.eval value66 (momentVector H) := by
  have heq : pivotMatrix66 = (fun u v => node66 (pivotPermutation66 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node66 = injectiveMoment H pivotMatrix66 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix66 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix66 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix66 (0 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix66 (0 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix66 (1 : Fin 4)) =
      Sparse.eval value13 (momentVector H) := by
    have heq : mergeFirst pivotMatrix66 (1 : Fin 4) = raw50 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical50 hH).trans (sound13 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix66 (2 : Fin 4)) =
      Sparse.eval value13 (momentVector H) := by
    have heq : mergeFirst pivotMatrix66 (2 : Fin 4) = raw47 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical47 hH).trans (sound13 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix66 (3 : Fin 4)) =
      Sparse.eval value12 (momentVector H) := by
    have heq : mergeFirst pivotMatrix66 (3 : Fin 4) = raw45 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical45 hH).trans (sound12 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node66 + (injectiveMoment H (mergeFirst pivotMatrix66 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix66 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix66 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix66 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value66, value12, value13, value16, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation67 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix67 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![1, -1], ![3, -3]]

theorem sound67 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node67 = Sparse.eval value67 (momentVector H) := by
  have heq : pivotMatrix67 = (fun u v => node67 (pivotPermutation67 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node67 = injectiveMoment H pivotMatrix67 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix67 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix67 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix67 (0 : Fin 4)) =
      Sparse.eval value12 (momentVector H) := by
    have heq : mergeFirst pivotMatrix67 (0 : Fin 4) = raw45 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical45 hH).trans (sound12 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix67 (1 : Fin 4)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix67 (1 : Fin 4) = raw198 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical198 hH).trans (sound8 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix67 (2 : Fin 4)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix67 (2 : Fin 4) = raw203 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical203 hH).trans (sound8 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix67 (3 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix67 (3 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node67 + (injectiveMoment H (mergeFirst pivotMatrix67 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix67 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix67 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix67 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value67, value12, value16, value8, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation68 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix68 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![2, -2], ![2, -2]]

theorem sound68 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node68 = Sparse.eval value68 (momentVector H) := by
  have heq : pivotMatrix68 = (fun u v => node68 (pivotPermutation68 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node68 = injectiveMoment H pivotMatrix68 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix68 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix68 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix68 (0 : Fin 4)) =
      Sparse.eval value13 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (0 : Fin 4) = raw47 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical47 hH).trans (sound13 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix68 (1 : Fin 4)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (1 : Fin 4) = raw199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical199 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix68 (2 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (2 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix68 (3 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix68 (3 : Fin 4) = raw210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical210 hH).trans (sound16 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node68 + (injectiveMoment H (mergeFirst pivotMatrix68 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix68 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix68 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix68 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value68, value13, value16, value9, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation69 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix69 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-4, 4], ![1, -1], ![1, -1], ![1, -1]]

theorem sound69 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node69 = Sparse.eval value69 (momentVector H) := by
  have heq : pivotMatrix69 = (fun u v => node69 (pivotPermutation69 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node69 = injectiveMoment H pivotMatrix69 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix69 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix69 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix69 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix69 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix69 (1 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix69 (1 : Fin 4) = raw213 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical213 hH).trans (sound16 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix69 (2 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix69 (2 : Fin 4) = raw210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical210 hH).trans (sound16 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix69 (3 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix69 (3 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node69 + (injectiveMoment H (mergeFirst pivotMatrix69 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix69 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix69 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix69 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value69, value16, value26, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation70 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix70 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![3, -1, -2]]

theorem sound70 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node70 = Sparse.eval value70 (momentVector H) := by
  have heq : pivotMatrix70 = (fun u v => node70 (pivotPermutation70 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node70 = injectiveMoment H pivotMatrix70 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix70 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix70 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix70 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix70 (0 : Fin 3) = raw312 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical312 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix70 (1 : Fin 3)) =
      Sparse.eval value17 (momentVector H) := by
    have heq : mergeFirst pivotMatrix70 (1 : Fin 3) = raw246 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical246 hH).trans (sound17 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix70 (2 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix70 (2 : Fin 3) = raw241 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical241 hH).trans (sound28 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node70 + (injectiveMoment H (mergeFirst pivotMatrix70 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix70 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix70 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value70, value17, value28, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation71 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix71 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, -1, 0], ![2, 2, -4]]

theorem sound71 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node71 = Sparse.eval value71 (momentVector H) := by
  have heq : pivotMatrix71 = (fun u v => node71 (pivotPermutation71 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node71 = injectiveMoment H pivotMatrix71 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix71 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix71 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix71 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix71 (0 : Fin 3) = raw328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical328 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix71 (1 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix71 (1 : Fin 3) = raw253 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical253 hH).trans (sound48 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix71 (2 : Fin 3)) =
      Sparse.eval value60 (momentVector H) := by
    have heq : mergeFirst pivotMatrix71 (2 : Fin 3) = raw250 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical250 hH).trans (sound60 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node71 + (injectiveMoment H (mergeFirst pivotMatrix71 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix71 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix71 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value71, value48, value59, value60, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation72 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix72 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, 2, -3], ![2, -1, -1]]

theorem sound72 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node72 = Sparse.eval value72 (momentVector H) := by
  have heq : pivotMatrix72 = (fun u v => node72 (pivotPermutation72 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node72 = injectiveMoment H pivotMatrix72 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix72 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix72 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix72 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix72 (0 : Fin 3) = raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical333 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix72 (1 : Fin 3)) =
      Sparse.eval value39 (momentVector H) := by
    have heq : mergeFirst pivotMatrix72 (1 : Fin 3) = raw258 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical258 hH).trans (sound39 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix72 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix72 (2 : Fin 3) = raw257 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical257 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node72 + (injectiveMoment H (mergeFirst pivotMatrix72 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix72 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix72 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value72, value27, value39, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation73 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix73 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 2, -2], ![2, 1, -3]]

theorem sound73 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node73 = Sparse.eval value73 (momentVector H) := by
  have heq : pivotMatrix73 = (fun u v => node73 (pivotPermutation73 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node73 = injectiveMoment H pivotMatrix73 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix73 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix73 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix73 (0 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix73 (0 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix73 (1 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix73 (1 : Fin 3) = raw255 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical255 hH).trans (sound30 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix73 (2 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix73 (2 : Fin 3) = raw241 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical241 hH).trans (sound28 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node73 + (injectiveMoment H (mergeFirst pivotMatrix73 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix73 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix73 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value73, value27, value28, value30, Sparse.eval] at hc ⊢
  linarith

theorem sound74 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node74 = Sparse.eval value74 (momentVector H) := by
  have hc : momentVector H 256 = injectiveMoment H node74 := rfl
  simp [value74, Sparse.eval, hc]

def pivotPermutation75 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix75 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 3, -3], ![2, 0, -2]]

theorem sound75 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node75 = Sparse.eval value75 (momentVector H) := by
  have heq : pivotMatrix75 = (fun u v => node75 (pivotPermutation75 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node75 = injectiveMoment H pivotMatrix75 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix75 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix75 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix75 (0 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix75 (0 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix75 (1 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix75 (1 : Fin 3) = raw257 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical257 hH).trans (sound27 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix75 (2 : Fin 3)) =
      Sparse.eval value17 (momentVector H) := by
    have heq : mergeFirst pivotMatrix75 (2 : Fin 3) = raw246 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical246 hH).trans (sound17 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node75 + (injectiveMoment H (mergeFirst pivotMatrix75 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix75 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix75 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value75, value17, value27, value28, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation76 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix76 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -2, 5], ![0, 3, -3], ![2, -1, -1]]

theorem sound76 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node76 = Sparse.eval value76 (momentVector H) := by
  have heq : pivotMatrix76 = (fun u v => node76 (pivotPermutation76 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node76 = injectiveMoment H pivotMatrix76 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix76 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix76 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix76 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix76 (0 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix76 (1 : Fin 3)) =
      Sparse.eval value39 (momentVector H) := by
    have heq : mergeFirst pivotMatrix76 (1 : Fin 3) = raw258 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical258 hH).trans (sound39 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix76 (2 : Fin 3)) =
      Sparse.eval value17 (momentVector H) := by
    have heq : mergeFirst pivotMatrix76 (2 : Fin 3) = raw246 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical246 hH).trans (sound17 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node76 + (injectiveMoment H (mergeFirst pivotMatrix76 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix76 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix76 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value76, value17, value32, value39, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation77 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix77 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![1, 0, -1], ![1, 3, -4]]

theorem sound77 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node77 = Sparse.eval value77 (momentVector H) := by
  have heq : pivotMatrix77 = (fun u v => node77 (pivotPermutation77 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node77 = injectiveMoment H pivotMatrix77 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix77 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix77 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix77 (0 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix77 (0 : Fin 3) = raw962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical962 hH).trans (sound49 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix77 (1 : Fin 3)) =
      Sparse.eval value39 (momentVector H) := by
    have heq : mergeFirst pivotMatrix77 (1 : Fin 3) = raw259 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical259 hH).trans (sound39 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix77 (2 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix77 (2 : Fin 3) = raw253 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical253 hH).trans (sound48 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node77 + (injectiveMoment H (mergeFirst pivotMatrix77 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix77 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix77 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value77, value39, value48, value49, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation78 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix78 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![1, 1, -2], ![1, 2, -3]]

theorem sound78 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node78 = Sparse.eval value78 (momentVector H) := by
  have heq : pivotMatrix78 = (fun u v => node78 (pivotPermutation78 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node78 = injectiveMoment H pivotMatrix78 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix78 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix78 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix78 (0 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix78 (0 : Fin 3) = raw963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical963 hH).trans (sound30 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix78 (1 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix78 (1 : Fin 3) = raw260 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical260 hH).trans (sound27 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix78 (2 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix78 (2 : Fin 3) = raw255 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical255 hH).trans (sound30 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node78 + (injectiveMoment H (mergeFirst pivotMatrix78 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix78 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix78 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value78, value27, value30, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation79 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix79 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![3, -1, -2]]

theorem sound79 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node79 = Sparse.eval value79 (momentVector H) := by
  have heq : pivotMatrix79 = (fun u v => node79 (pivotPermutation79 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node79 = injectiveMoment H pivotMatrix79 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix79 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix79 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix79 (0 : Fin 3)) =
      Sparse.eval value17 (momentVector H) := by
    have heq : mergeFirst pivotMatrix79 (0 : Fin 3) = raw246 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical246 hH).trans (sound17 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix79 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix79 (1 : Fin 3) = raw312 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical312 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix79 (2 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix79 (2 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node79 + (injectiveMoment H (mergeFirst pivotMatrix79 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix79 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix79 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value79, value17, value18, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation80 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix80 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![1, 3, -4], ![2, -1, -1]]

theorem sound80 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node80 = Sparse.eval value80 (momentVector H) := by
  have heq : pivotMatrix80 = (fun u v => node80 (pivotPermutation80 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node80 = injectiveMoment H pivotMatrix80 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix80 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix80 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix80 (0 : Fin 3)) =
      Sparse.eval value39 (momentVector H) := by
    have heq : mergeFirst pivotMatrix80 (0 : Fin 3) = raw258 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical258 hH).trans (sound39 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix80 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix80 (1 : Fin 3) = raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical333 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix80 (2 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix80 (2 : Fin 3) = raw335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical335 hH).trans (sound38 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node80 + (injectiveMoment H (mergeFirst pivotMatrix80 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix80 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix80 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value80, value38, value39, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation81 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix81 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![3, -2, -1]]

theorem sound81 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node81 = Sparse.eval value81 (momentVector H) := by
  have heq : pivotMatrix81 = (fun u v => node81 (pivotPermutation81 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node81 = injectiveMoment H pivotMatrix81 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix81 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix81 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix81 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix81 (0 : Fin 3) = raw556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical556 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix81 (1 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix81 (1 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix81 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix81 (2 : Fin 3) = raw312 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical312 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node81 + (injectiveMoment H (mergeFirst pivotMatrix81 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix81 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix81 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value81, value18, value32, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation82 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix82 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -2, 1], ![2, 2, -4]]

theorem sound82 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node82 = Sparse.eval value82 (momentVector H) := by
  have heq : pivotMatrix82 = (fun u v => node82 (pivotPermutation82 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node82 = injectiveMoment H pivotMatrix82 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix82 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix82 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix82 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix82 (0 : Fin 3) = raw577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical577 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix82 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix82 (1 : Fin 3) = raw328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical328 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix82 (2 : Fin 3)) =
      Sparse.eval value39 (momentVector H) := by
    have heq : mergeFirst pivotMatrix82 (2 : Fin 3) = raw324 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical324 hH).trans (sound39 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node82 + (injectiveMoment H (mergeFirst pivotMatrix82 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix82 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix82 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value82, value32, value39, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation83 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix83 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, 2, -3], ![2, -2, 0]]

theorem sound83 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node83 = Sparse.eval value83 (momentVector H) := by
  have heq : pivotMatrix83 = (fun u v => node83 (pivotPermutation83 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node83 = injectiveMoment H pivotMatrix83 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix83 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix83 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix83 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix83 (0 : Fin 3) = raw582 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical582 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix83 (1 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix83 (1 : Fin 3) = raw335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical335 hH).trans (sound38 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix83 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix83 (2 : Fin 3) = raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical333 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node83 + (injectiveMoment H (mergeFirst pivotMatrix83 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix83 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix83 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value83, value37, value38, value40, Sparse.eval] at hc ⊢
  linarith

theorem sound84 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node84 = Sparse.eval value84 (momentVector H) := by
  have hc : momentVector H 259 = injectiveMoment H node84 := rfl
  simp [value84, Sparse.eval, hc]

theorem sound85 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node85 = Sparse.eval value85 (momentVector H) := by
  have hc : momentVector H 59 = injectiveMoment H node85 := rfl
  simp [value85, Sparse.eval, hc]

theorem sound86 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node86 = Sparse.eval value86 (momentVector H) := by
  have hc : momentVector H 260 = injectiveMoment H node86 := rfl
  simp [value86, Sparse.eval, hc]

def pivotPermutation87 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix87 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![0, 3, -3], ![2, -1, -1]]

theorem sound87 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node87 = Sparse.eval value87 (momentVector H) := by
  have heq : pivotMatrix87 = (fun u v => node87 (pivotPermutation87 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node87 = injectiveMoment H pivotMatrix87 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix87 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix87 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix87 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix87 (0 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix87 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix87 (1 : Fin 3) = raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical333 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix87 (2 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix87 (2 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node87 + (injectiveMoment H (mergeFirst pivotMatrix87 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix87 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix87 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value87, value18, value32, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation88 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix88 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-3, -1, 4], ![0, 3, -3], ![2, -2, 0]]

theorem sound88 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node88 = Sparse.eval value88 (momentVector H) := by
  have heq : pivotMatrix88 = (fun u v => node88 (pivotPermutation88 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node88 = injectiveMoment H pivotMatrix88 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix88 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix88 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix88 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix88 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix88 (1 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix88 (1 : Fin 3) = raw335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical335 hH).trans (sound38 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix88 (2 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix88 (2 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node88 + (injectiveMoment H (mergeFirst pivotMatrix88 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix88 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix88 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value88, value18, value37, value38, Sparse.eval] at hc ⊢
  linarith

theorem sound89 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node89 = Sparse.eval value89 (momentVector H) := by
  have hc : momentVector H 262 = injectiveMoment H node89 := rfl
  simp [value89, Sparse.eval, hc]

def pivotPermutation90 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix90 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -1, 4], ![1, -1, 0], ![1, 3, -4]]

theorem sound90 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node90 = Sparse.eval value90 (momentVector H) := by
  have heq : pivotMatrix90 = (fun u v => node90 (pivotPermutation90 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node90 = injectiveMoment H pivotMatrix90 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix90 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix90 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix90 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix90 (1 : Fin 3)) =
      Sparse.eval value38 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (1 : Fin 3) = raw336 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical336 hH).trans (sound38 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix90 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix90 (2 : Fin 3) = raw328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical328 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node90 + (injectiveMoment H (mergeFirst pivotMatrix90 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix90 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix90 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value90, value38, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound91 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node91 = Sparse.eval value91 (momentVector H) := by
  have hc : momentVector H 264 = injectiveMoment H node91 := rfl
  simp [value91, Sparse.eval, hc]

def pivotPermutation92 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix92 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![3, -2, -1]]

theorem sound92 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node92 = Sparse.eval value92 (momentVector H) := by
  have heq : pivotMatrix92 = (fun u v => node92 (pivotPermutation92 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node92 = injectiveMoment H pivotMatrix92 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix92 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix92 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix92 (0 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix92 (0 : Fin 3) = raw320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical320 hH).trans (sound18 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix92 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix92 (1 : Fin 3) = raw556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical556 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix92 (2 : Fin 3)) =
      Sparse.eval value19 (momentVector H) := by
    have heq : mergeFirst pivotMatrix92 (2 : Fin 3) = raw565 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical565 hH).trans (sound19 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node92 + (injectiveMoment H (mergeFirst pivotMatrix92 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix92 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix92 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value92, value18, value19, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation93 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix93 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![3, -3, 0]]

theorem sound93 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node93 = Sparse.eval value93 (momentVector H) := by
  have heq : pivotMatrix93 = (fun u v => node93 (pivotPermutation93 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node93 = injectiveMoment H pivotMatrix93 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix93 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix93 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix93 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix93 (0 : Fin 3) = raw795 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical795 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix93 (1 : Fin 3)) =
      Sparse.eval value19 (momentVector H) := by
    have heq : mergeFirst pivotMatrix93 (1 : Fin 3) = raw565 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical565 hH).trans (sound19 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix93 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix93 (2 : Fin 3) = raw556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical556 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node93 + (injectiveMoment H (mergeFirst pivotMatrix93 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix93 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix93 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value93, value19, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation94 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix94 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, -3, 2], ![2, 2, -4]]

theorem sound94 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node94 = Sparse.eval value94 (momentVector H) := by
  have heq : pivotMatrix94 = (fun u v => node94 (pivotPermutation94 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node94 = injectiveMoment H pivotMatrix94 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix94 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix94 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix94 (0 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix94 (0 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix94 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix94 (1 : Fin 3) = raw577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical577 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix94 (2 : Fin 3)) =
      Sparse.eval value17 (momentVector H) := by
    have heq : mergeFirst pivotMatrix94 (2 : Fin 3) = raw572 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical572 hH).trans (sound17 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node94 + (injectiveMoment H (mergeFirst pivotMatrix94 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix94 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix94 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value94, value17, value20, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation95 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix95 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![1, 2, -3], ![2, -3, 1]]

theorem sound95 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node95 = Sparse.eval value95 (momentVector H) := by
  have heq : pivotMatrix95 = (fun u v => node95 (pivotPermutation95 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node95 = injectiveMoment H pivotMatrix95 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix95 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix95 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix95 (0 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix95 (0 : Fin 3) = raw814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical814 hH).trans (sound21 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix95 (1 : Fin 3)) =
      Sparse.eval value18 (momentVector H) := by
    have heq : mergeFirst pivotMatrix95 (1 : Fin 3) = raw583 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical583 hH).trans (sound18 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix95 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix95 (2 : Fin 3) = raw582 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical582 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node95 + (injectiveMoment H (mergeFirst pivotMatrix95 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix95 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix95 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value95, value18, value21, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound96 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node96 = Sparse.eval value96 (momentVector H) := by
  have hc : momentVector H 266 = injectiveMoment H node96 := rfl
  simp [value96, Sparse.eval, hc]

theorem sound97 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node97 = Sparse.eval value97 (momentVector H) := by
  have hc : momentVector H 61 = injectiveMoment H node97 := rfl
  simp [value97, Sparse.eval, hc]

theorem sound98 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node98 = Sparse.eval value98 (momentVector H) := by
  have hc : momentVector H 62 = injectiveMoment H node98 := rfl
  simp [value98, Sparse.eval, hc]

theorem sound99 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node99 = Sparse.eval value99 (momentVector H) := by
  have hc : momentVector H 267 = injectiveMoment H node99 := rfl
  simp [value99, Sparse.eval, hc]

theorem sound100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node100 = Sparse.eval value100 (momentVector H) := by
  have hc : momentVector H 268 = injectiveMoment H node100 := rfl
  simp [value100, Sparse.eval, hc]

theorem sound101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node101 = Sparse.eval value101 (momentVector H) := by
  have hc : momentVector H 63 = injectiveMoment H node101 := rfl
  simp [value101, Sparse.eval, hc]

def pivotPermutation102 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix102 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![2, 2, -4]]

theorem sound102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node102 = Sparse.eval value102 (momentVector H) := by
  have heq : pivotMatrix102 = (fun u v => node102 (pivotPermutation102 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node102 = injectiveMoment H pivotMatrix102 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix102 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix102 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix102 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix102 (0 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix102 (1 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix102 (1 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix102 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix102 (2 : Fin 3) = raw719 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical719 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node102 + (injectiveMoment H (mergeFirst pivotMatrix102 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix102 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix102 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value102, value20, value31, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node103 = Sparse.eval value103 (momentVector H) := by
  have hc : momentVector H 64 = injectiveMoment H node103 := rfl
  simp [value103, Sparse.eval, hc]

theorem sound104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node104 = Sparse.eval value104 (momentVector H) := by
  have hc : momentVector H 271 = injectiveMoment H node104 := rfl
  simp [value104, Sparse.eval, hc]

def pivotPermutation105 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix105 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![3, -2, -1]]

theorem sound105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node105 = Sparse.eval value105 (momentVector H) := by
  have heq : pivotMatrix105 = (fun u v => node105 (pivotPermutation105 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node105 = injectiveMoment H pivotMatrix105 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix105 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix105 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix105 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix105 (0 : Fin 3) = raw556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical556 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix105 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix105 (1 : Fin 3) = raw784 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical784 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix105 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix105 (2 : Fin 3) = raw795 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical795 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node105 + (injectiveMoment H (mergeFirst pivotMatrix105 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix105 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix105 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value105, value37, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation106 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix106 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, -2, 1], ![2, 2, -4]]

theorem sound106 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node106 = Sparse.eval value106 (momentVector H) := by
  have heq : pivotMatrix106 = (fun u v => node106 (pivotPermutation106 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node106 = injectiveMoment H pivotMatrix106 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix106 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix106 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix106 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix106 (0 : Fin 3) = raw577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical577 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix106 (1 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix106 (1 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix106 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix106 (2 : Fin 3) = raw806 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical806 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node106 + (injectiveMoment H (mergeFirst pivotMatrix106 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix106 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix106 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value106, value20, value32, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation107 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix107 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![1, 2, -3], ![2, -2, 0]]

theorem sound107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node107 = Sparse.eval value107 (momentVector H) := by
  have heq : pivotMatrix107 = (fun u v => node107 (pivotPermutation107 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node107 = injectiveMoment H pivotMatrix107 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix107 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix107 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix107 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix107 (0 : Fin 3) = raw582 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical582 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix107 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix107 (1 : Fin 3) = raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical813 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix107 (2 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix107 (2 : Fin 3) = raw814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical814 hH).trans (sound21 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node107 + (injectiveMoment H (mergeFirst pivotMatrix107 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix107 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix107 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value107, value21, value36, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation108 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix108 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, -3, 2], ![2, 1, -3]]

theorem sound108 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node108 = Sparse.eval value108 (momentVector H) := by
  have heq : pivotMatrix108 = (fun u v => node108 (pivotPermutation108 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node108 = injectiveMoment H pivotMatrix108 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix108 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix108 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix108 (0 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix108 (0 : Fin 3) = raw838 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical838 hH).trans (sound21 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix108 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix108 (1 : Fin 3) = raw806 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical806 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix108 (2 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix108 (2 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node108 + (injectiveMoment H (mergeFirst pivotMatrix108 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix108 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix108 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value108, value20, value21, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation109 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix109 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![1, 1, -2], ![2, -3, 1]]

theorem sound109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node109 = Sparse.eval value109 (momentVector H) := by
  have heq : pivotMatrix109 = (fun u v => node109 (pivotPermutation109 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node109 = injectiveMoment H pivotMatrix109 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix109 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix109 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix109 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (0 : Fin 3) = raw840 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical840 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix109 (1 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (1 : Fin 3) = raw814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical814 hH).trans (sound21 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix109 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (2 : Fin 3) = raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical813 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node109 + (injectiveMoment H (mergeFirst pivotMatrix109 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix109 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix109 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value109, value21, value36, value43, Sparse.eval] at hc ⊢
  linarith

theorem sound110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node110 = Sparse.eval value110 (momentVector H) := by
  have hc : momentVector H 65 = injectiveMoment H node110 := rfl
  simp [value110, Sparse.eval, hc]

theorem sound111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node111 = Sparse.eval value111 (momentVector H) := by
  have hc : momentVector H 33 = injectiveMoment H node111 := rfl
  simp [value111, Sparse.eval, hc]

theorem sound112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node112 = Sparse.eval value112 (momentVector H) := by
  have hc : momentVector H 273 = injectiveMoment H node112 := rfl
  simp [value112, Sparse.eval, hc]

def pivotPermutation113 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix113 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![1, -3, 2], ![1, 3, -4]]

theorem sound113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node113 = Sparse.eval value113 (momentVector H) := by
  have heq : pivotMatrix113 = (fun u v => node113 (pivotPermutation113 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node113 = injectiveMoment H pivotMatrix113 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix113 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix113 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix113 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix113 (0 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix113 (1 : Fin 3)) =
      Sparse.eval value22 (momentVector H) := by
    have heq : mergeFirst pivotMatrix113 (1 : Fin 3) = raw815 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical815 hH).trans (sound22 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix113 (2 : Fin 3)) =
      Sparse.eval value20 (momentVector H) := by
    have heq : mergeFirst pivotMatrix113 (2 : Fin 3) = raw801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical801 hH).trans (sound20 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node113 + (injectiveMoment H (mergeFirst pivotMatrix113 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix113 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix113 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value113, value20, value22, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node114 = Sparse.eval value114 (momentVector H) := by
  have hc : momentVector H 66 = injectiveMoment H node114 := rfl
  simp [value114, Sparse.eval, hc]

theorem sound115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node115 = Sparse.eval value115 (momentVector H) := by
  have hc : momentVector H 275 = injectiveMoment H node115 := rfl
  simp [value115, Sparse.eval, hc]

def pivotPermutation116 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix116 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![-2, 2], ![1, -1], ![3, -3]]

theorem sound116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node116 = Sparse.eval value116 (momentVector H) := by
  have heq : pivotMatrix116 = (fun u v => node116 (pivotPermutation116 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node116 = injectiveMoment H pivotMatrix116 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix116 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix116 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix116 (0 : Fin 4)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix116 (0 : Fin 4) = raw5112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5112 hH).trans (sound25 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix116 (1 : Fin 4)) =
      Sparse.eval value24 (momentVector H) := by
    have heq : mergeFirst pivotMatrix116 (1 : Fin 4) = raw869 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical869 hH).trans (sound24 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix116 (2 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix116 (2 : Fin 4) = raw852 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical852 hH).trans (sound23 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix116 (3 : Fin 4)) =
      Sparse.eval value15 (momentVector H) := by
    have heq : mergeFirst pivotMatrix116 (3 : Fin 4) = raw850 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical850 hH).trans (sound15 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node116 + (injectiveMoment H (mergeFirst pivotMatrix116 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix116 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix116 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix116 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value116, value15, value23, value24, value25, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation117 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix117 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-3, 3], ![-2, 2], ![2, -2], ![2, -2]]

theorem sound117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node117 = Sparse.eval value117 (momentVector H) := by
  have heq : pivotMatrix117 = (fun u v => node117 (pivotPermutation117 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node117 = injectiveMoment H pivotMatrix117 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix117 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix117 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix117 (0 : Fin 4)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (0 : Fin 4) = raw5116 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5116 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix117 (1 : Fin 4)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (1 : Fin 4) = raw872 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical872 hH).trans (sound25 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix117 (2 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (2 : Fin 4) = raw853 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical853 hH).trans (sound23 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix117 (3 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (3 : Fin 4) = raw852 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical852 hH).trans (sound23 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node117 + (injectiveMoment H (mergeFirst pivotMatrix117 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value117, value23, value25, value45, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation118 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix118 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]

theorem sound118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node118 = Sparse.eval value118 (momentVector H) := by
  have heq : pivotMatrix118 = (fun u v => node118 (pivotPermutation118 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node118 = injectiveMoment H pivotMatrix118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix118 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix118 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix118 (0 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (0 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix118 (1 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (1 : Fin 4) = raw895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical895 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix118 (2 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (2 : Fin 4) = raw909 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical909 hH).trans (sound10 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix118 (3 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (3 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node118 + (injectiveMoment H (mergeFirst pivotMatrix118 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value118, value10, value16, value26, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation119 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix119 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![2, 1, -3]]

theorem sound119 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node119 = Sparse.eval value119 (momentVector H) := by
  have heq : pivotMatrix119 = (fun u v => node119 (pivotPermutation119 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node119 = injectiveMoment H pivotMatrix119 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix119 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix119 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix119 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix119 (0 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix119 (1 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix119 (1 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix119 (2 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix119 (2 : Fin 3) = raw946 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical946 hH).trans (sound48 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node119 + (injectiveMoment H (mergeFirst pivotMatrix119 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix119 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix119 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value119, value27, value48, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation120 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix120 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 2, -2], ![2, 0, -2]]

theorem sound120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node120 = Sparse.eval value120 (momentVector H) := by
  have heq : pivotMatrix120 = (fun u v => node120 (pivotPermutation120 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node120 = injectiveMoment H pivotMatrix120 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix120 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix120 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix120 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix120 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix120 (1 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix120 (1 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix120 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix120 (2 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node120 + (injectiveMoment H (mergeFirst pivotMatrix120 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix120 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix120 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value120, value27, value28, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation121 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix121 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 3, -3], ![2, -1, -1]]

theorem sound121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node121 = Sparse.eval value121 (momentVector H) := by
  have heq : pivotMatrix121 = (fun u v => node121 (pivotPermutation121 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node121 = injectiveMoment H pivotMatrix121 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix121 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix121 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix121 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix121 (0 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix121 (1 : Fin 3)) =
      Sparse.eval value29 (momentVector H) := by
    have heq : mergeFirst pivotMatrix121 (1 : Fin 3) = raw960 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical960 hH).trans (sound29 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix121 (2 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix121 (2 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node121 + (injectiveMoment H (mergeFirst pivotMatrix121 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix121 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix121 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value121, value28, value29, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation122 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix122 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![1, -1, 0], ![1, 3, -4]]

theorem sound122 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node122 = Sparse.eval value122 (momentVector H) := by
  have heq : pivotMatrix122 = (fun u v => node122 (pivotPermutation122 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node122 = injectiveMoment H pivotMatrix122 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix122 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix122 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix122 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix122 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix122 (1 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix122 (1 : Fin 3) = raw962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical962 hH).trans (sound49 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix122 (2 : Fin 3)) =
      Sparse.eval value55 (momentVector H) := by
    have heq : mergeFirst pivotMatrix122 (2 : Fin 3) = raw961 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical961 hH).trans (sound55 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node122 + (injectiveMoment H (mergeFirst pivotMatrix122 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix122 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix122 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value122, value49, value55, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation123 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix123 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![1, 0, -1], ![1, 2, -3]]

theorem sound123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node123 = Sparse.eval value123 (momentVector H) := by
  have heq : pivotMatrix123 = (fun u v => node123 (pivotPermutation123 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node123 = injectiveMoment H pivotMatrix123 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix123 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix123 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix123 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix123 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix123 (1 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix123 (1 : Fin 3) = raw963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical963 hH).trans (sound30 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix123 (2 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix123 (2 : Fin 3) = raw962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical962 hH).trans (sound49 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node123 + (injectiveMoment H (mergeFirst pivotMatrix123 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix123 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix123 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value123, value30, value49, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation124 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix124 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![1, 1, -2], ![1, 1, -2]]

theorem sound124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node124 = Sparse.eval value124 (momentVector H) := by
  have heq : pivotMatrix124 = (fun u v => node124 (pivotPermutation124 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node124 = injectiveMoment H pivotMatrix124 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix124 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix124 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix124 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix124 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix124 (1 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix124 (1 : Fin 3) = raw964 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical964 hH).trans (sound30 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix124 (2 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix124 (2 : Fin 3) = raw963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical963 hH).trans (sound30 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node124 + (injectiveMoment H (mergeFirst pivotMatrix124 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix124 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix124 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value124, value30, value35, Sparse.eval] at hc ⊢
  linarith

theorem sound125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node125 = Sparse.eval value125 (momentVector H) := by
  have hc : momentVector H 277 = injectiveMoment H node125 := rfl
  simp [value125, Sparse.eval, hc]

def pivotPermutation126 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix126 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -3, 5], ![0, 2, -2], ![1, 2, -3]]

theorem sound126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node126 = Sparse.eval value126 (momentVector H) := by
  have heq : pivotMatrix126 = (fun u v => node126 (pivotPermutation126 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node126 = injectiveMoment H pivotMatrix126 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix126 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix126 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix126 (0 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix126 (0 : Fin 3) = raw5483 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5483 hH).trans (sound48 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix126 (1 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix126 (1 : Fin 3) = raw963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical963 hH).trans (sound30 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix126 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix126 (2 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node126 + (injectiveMoment H (mergeFirst pivotMatrix126 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix126 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix126 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value126, value27, value30, value48, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation127 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix127 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -3, 5], ![0, 2, -2], ![1, 1, -2]]

theorem sound127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node127 = Sparse.eval value127 (momentVector H) := by
  have heq : pivotMatrix127 = (fun u v => node127 (pivotPermutation127 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node127 = injectiveMoment H pivotMatrix127 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix127 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix127 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix127 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix127 (0 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix127 (1 : Fin 3)) =
      Sparse.eval value30 (momentVector H) := by
    have heq : mergeFirst pivotMatrix127 (1 : Fin 3) = raw964 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical964 hH).trans (sound30 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix127 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix127 (2 : Fin 3) = raw955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical955 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node127 + (injectiveMoment H (mergeFirst pivotMatrix127 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix127 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix127 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value127, value27, value30, value52, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
