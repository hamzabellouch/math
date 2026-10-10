import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical92
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical207
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical210
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2432 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2432 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2432 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2432 = Sparse.eval value2432 (momentVector H) := by
  have heq : pivotMatrix2432 = (fun u v => node2432 (pivotPermutation2432 u) v) := by apply Matrix.ext; unfold pivotMatrix2432 node2432 pivotPermutation2432; decide +kernel
  have hmoment : injectiveMoment H node2432 = injectiveMoment H pivotMatrix2432 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2432 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2432 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2432 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2432 (0 : Fin 4) = raw6635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2432 raw6635; decide +kernel
    rw [heq]
    exact (canonical6635 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2432 (1 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2432 (1 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2432 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2432 (2 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2432 (2 : Fin 4) = raw5739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2432 raw5739; decide +kernel
    rw [heq]
    exact (canonical5739 hH).trans (sound832 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2432 (3 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2432 (3 : Fin 4) = raw5737 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2432 raw5737; decide +kernel
    rw [heq]
    exact (canonical5737 hH).trans (sound828 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2432 + (injectiveMoment H (mergeFirst pivotMatrix2432 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2432 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2432 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2432 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2432, value1110, value828, value832, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2433 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2433 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

theorem sound2433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2433 = Sparse.eval value2433 (momentVector H) := by
  have heq : pivotMatrix2433 = (fun u v => node2433 (pivotPermutation2433 u) v) := by apply Matrix.ext; unfold pivotMatrix2433 node2433 pivotPermutation2433; decide +kernel
  have hmoment : injectiveMoment H node2433 = injectiveMoment H pivotMatrix2433 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2433 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2433 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2433 (0 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2433 (0 : Fin 4) = raw5659 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2433 raw5659; decide +kernel
    rw [heq]
    exact (canonical5659 hH).trans (sound1042 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2433 (1 : Fin 4)) =
      Sparse.eval value826 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2433 (1 : Fin 4) = raw5735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2433 raw5735; decide +kernel
    rw [heq]
    exact (canonical5735 hH).trans (sound826 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2433 (2 : Fin 4)) =
      Sparse.eval value834 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2433 (2 : Fin 4) = raw5747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2433 raw5747; decide +kernel
    rw [heq]
    exact (canonical5747 hH).trans (sound834 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2433 (3 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2433 (3 : Fin 4) = raw5751 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2433 raw5751; decide +kernel
    rw [heq]
    exact (canonical5751 hH).trans (sound1116 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2433 + (injectiveMoment H (mergeFirst pivotMatrix2433 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2433 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2433 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2433 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2433, value1042, value1116, value826, value834, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2434 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2434 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

theorem sound2434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2434 = Sparse.eval value2434 (momentVector H) := by
  have heq : pivotMatrix2434 = (fun u v => node2434 (pivotPermutation2434 u) v) := by apply Matrix.ext; unfold pivotMatrix2434 node2434 pivotPermutation2434; decide +kernel
  have hmoment : injectiveMoment H node2434 = injectiveMoment H pivotMatrix2434 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2434 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2434 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2434 (0 : Fin 4)) =
      Sparse.eval value963 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2434 (0 : Fin 4) = raw5660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2434 raw5660; decide +kernel
    rw [heq]
    exact (canonical5660 hH).trans (sound963 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2434 (1 : Fin 4)) =
      Sparse.eval value827 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2434 (1 : Fin 4) = raw5736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2434 raw5736; decide +kernel
    rw [heq]
    exact (canonical5736 hH).trans (sound827 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2434 (2 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2434 (2 : Fin 4) = raw5751 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2434 raw5751; decide +kernel
    rw [heq]
    exact (canonical5751 hH).trans (sound1116 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2434 (3 : Fin 4)) =
      Sparse.eval value1259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2434 (3 : Fin 4) = raw5752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2434 raw5752; decide +kernel
    rw [heq]
    exact (canonical5752 hH).trans (sound1259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2434 + (injectiveMoment H (mergeFirst pivotMatrix2434 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2434 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2434 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2434 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2434, value1116, value1259, value827, value963, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2435 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2435 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem sound2435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2435 = Sparse.eval value2435 (momentVector H) := by
  have heq : pivotMatrix2435 = (fun u v => node2435 (pivotPermutation2435 u) v) := by apply Matrix.ext; unfold pivotMatrix2435 node2435 pivotPermutation2435; decide +kernel
  have hmoment : injectiveMoment H node2435 = injectiveMoment H pivotMatrix2435 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2435 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2435 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2435 (0 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2435 (0 : Fin 4) = raw5661 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2435 raw5661; decide +kernel
    rw [heq]
    exact (canonical5661 hH).trans (sound1032 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2435 (1 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2435 (1 : Fin 4) = raw5738 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2435 raw5738; decide +kernel
    rw [heq]
    exact (canonical5738 hH).trans (sound831 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2435 (2 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2435 (2 : Fin 4) = raw5753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2435 raw5753; decide +kernel
    rw [heq]
    exact (canonical5753 hH).trans (sound837 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2435 (3 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2435 (3 : Fin 4) = raw5754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2435 raw5754; decide +kernel
    rw [heq]
    exact (canonical5754 hH).trans (sound1284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2435 + (injectiveMoment H (mergeFirst pivotMatrix2435 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2435 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2435 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2435 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2435, value1032, value1284, value831, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2436 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2436 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem sound2436 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2436 = Sparse.eval value2436 (momentVector H) := by
  have heq : pivotMatrix2436 = (fun u v => node2436 (pivotPermutation2436 u) v) := by apply Matrix.ext; unfold pivotMatrix2436 node2436 pivotPermutation2436; decide +kernel
  have hmoment : injectiveMoment H node2436 = injectiveMoment H pivotMatrix2436 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2436 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2436 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2436 (0 : Fin 4)) =
      Sparse.eval value1199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2436 (0 : Fin 4) = raw5662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2436 raw5662; decide +kernel
    rw [heq]
    exact (canonical5662 hH).trans (sound1199 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2436 (1 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2436 (1 : Fin 4) = raw5739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2436 raw5739; decide +kernel
    rw [heq]
    exact (canonical5739 hH).trans (sound832 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2436 (2 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2436 (2 : Fin 4) = raw5754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2436 raw5754; decide +kernel
    rw [heq]
    exact (canonical5754 hH).trans (sound1284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2436 (3 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2436 (3 : Fin 4) = raw5755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2436 raw5755; decide +kernel
    rw [heq]
    exact (canonical5755 hH).trans (sound1109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2436 + (injectiveMoment H (mergeFirst pivotMatrix2436 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2436 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2436 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2436 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2436, value1109, value1199, value1284, value832, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2437 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2437 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2437 = Sparse.eval value2437 (momentVector H) := by
  have heq : pivotMatrix2437 = (fun u v => node2437 (pivotPermutation2437 u) v) := by apply Matrix.ext; unfold pivotMatrix2437 node2437 pivotPermutation2437; decide +kernel
  have hmoment : injectiveMoment H node2437 = injectiveMoment H pivotMatrix2437 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2437 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2437 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2437 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2437 (0 : Fin 4) = raw5663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2437 raw5663; decide +kernel
    rw [heq]
    exact (canonical5663 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2437 (1 : Fin 4)) =
      Sparse.eval value833 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2437 (1 : Fin 4) = raw5740 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2437 raw5740; decide +kernel
    rw [heq]
    exact (canonical5740 hH).trans (sound833 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2437 (2 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2437 (2 : Fin 4) = raw5755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2437 raw5755; decide +kernel
    rw [heq]
    exact (canonical5755 hH).trans (sound1109 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2437 (3 : Fin 4)) =
      Sparse.eval value826 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2437 (3 : Fin 4) = raw5756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2437 raw5756; decide +kernel
    rw [heq]
    exact (canonical5756 hH).trans (sound826 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2437 + (injectiveMoment H (mergeFirst pivotMatrix2437 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2437 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2437 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2437 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2437, value1031, value1109, value826, value833, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2438 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2438 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem sound2438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2438 = Sparse.eval value2438 (momentVector H) := by
  have heq : pivotMatrix2438 = (fun u v => node2438 (pivotPermutation2438 u) v) := by apply Matrix.ext; unfold pivotMatrix2438 node2438 pivotPermutation2438; decide +kernel
  have hmoment : injectiveMoment H node2438 = injectiveMoment H pivotMatrix2438 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2438 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2438 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2438 (0 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2438 (0 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2438 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2438 (1 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2438 (1 : Fin 4) = raw5758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2438 raw5758; decide +kernel
    rw [heq]
    exact (canonical5758 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2438 (2 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2438 (2 : Fin 4) = raw5765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2438 raw5765; decide +kernel
    rw [heq]
    exact (canonical5765 hH).trans (sound1260 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2438 (3 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2438 (3 : Fin 4) = raw5766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2438 raw5766; decide +kernel
    rw [heq]
    exact (canonical5766 hH).trans (sound1047 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2438 + (injectiveMoment H (mergeFirst pivotMatrix2438 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2438 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2438 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2438 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2438, value1047, value1260, value283, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2439 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2439 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2439 = Sparse.eval value2439 (momentVector H) := by
  have heq : pivotMatrix2439 = (fun u v => node2439 (pivotPermutation2439 u) v) := by apply Matrix.ext; unfold pivotMatrix2439 node2439 pivotPermutation2439; decide +kernel
  have hmoment : injectiveMoment H node2439 = injectiveMoment H pivotMatrix2439 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2439 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2439 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2439 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2439 (0 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2439 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2439 (1 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2439 (1 : Fin 4) = raw5759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2439 raw5759; decide +kernel
    rw [heq]
    exact (canonical5759 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2439 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2439 (2 : Fin 4) = raw5768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2439 raw5768; decide +kernel
    rw [heq]
    exact (canonical5768 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2439 (3 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2439 (3 : Fin 4) = raw5769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2439 raw5769; decide +kernel
    rw [heq]
    exact (canonical5769 hH).trans (sound1265 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2439 + (injectiveMoment H (mergeFirst pivotMatrix2439 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2439 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2439 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2439 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2439, value1053, value1265, value284, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2440 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2440 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2440 = Sparse.eval value2440 (momentVector H) := by
  have heq : pivotMatrix2440 = (fun u v => node2440 (pivotPermutation2440 u) v) := by apply Matrix.ext; unfold pivotMatrix2440 node2440 pivotPermutation2440; decide +kernel
  have hmoment : injectiveMoment H node2440 = injectiveMoment H pivotMatrix2440 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2440 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2440 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2440 (0 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2440 (0 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2440 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2440 (1 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2440 (1 : Fin 4) = raw5760 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2440 raw5760; decide +kernel
    rw [heq]
    exact (canonical5760 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2440 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2440 (2 : Fin 4) = raw5769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2440 raw5769; decide +kernel
    rw [heq]
    exact (canonical5769 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2440 (3 : Fin 4)) =
      Sparse.eval value840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2440 (3 : Fin 4) = raw5770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2440 raw5770; decide +kernel
    rw [heq]
    exact (canonical5770 hH).trans (sound840 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2440 + (injectiveMoment H (mergeFirst pivotMatrix2440 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2440 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2440 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2440 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2440, value1221, value1265, value291, value840, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2441 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2441 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem sound2441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2441 = Sparse.eval value2441 (momentVector H) := by
  have heq : pivotMatrix2441 = (fun u v => node2441 (pivotPermutation2441 u) v) := by apply Matrix.ext; unfold pivotMatrix2441 node2441 pivotPermutation2441; decide +kernel
  have hmoment : injectiveMoment H node2441 = injectiveMoment H pivotMatrix2441 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2441 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2441 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2441 (0 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2441 (0 : Fin 4) = raw5707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2441 raw5707; decide +kernel
    rw [heq]
    exact (canonical5707 hH).trans (sound1041 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2441 (1 : Fin 4)) =
      Sparse.eval value836 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2441 (1 : Fin 4) = raw5776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2441 raw5776; decide +kernel
    rw [heq]
    exact (canonical5776 hH).trans (sound836 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2441 (2 : Fin 4)) =
      Sparse.eval value836 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2441 (2 : Fin 4) = raw5781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2441 raw5781; decide +kernel
    rw [heq]
    exact (canonical5781 hH).trans (sound836 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2441 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2441 (3 : Fin 4) = raw5782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2441 raw5782; decide +kernel
    rw [heq]
    exact (canonical5782 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2441 + (injectiveMoment H (mergeFirst pivotMatrix2441 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2441 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2441 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2441 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2441, value1040, value1041, value836, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2442 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2442 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound2442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2442 = Sparse.eval value2442 (momentVector H) := by
  have heq : pivotMatrix2442 = (fun u v => node2442 (pivotPermutation2442 u) v) := by apply Matrix.ext; unfold pivotMatrix2442 node2442 pivotPermutation2442; decide +kernel
  have hmoment : injectiveMoment H node2442 = injectiveMoment H pivotMatrix2442 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2442 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2442 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2442 (0 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2442 (0 : Fin 4) = raw5708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2442 raw5708; decide +kernel
    rw [heq]
    exact (canonical5708 hH).trans (sound1043 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2442 (1 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2442 (1 : Fin 4) = raw5777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2442 raw5777; decide +kernel
    rw [heq]
    exact (canonical5777 hH).trans (sound845 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2442 (2 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2442 (2 : Fin 4) = raw5782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2442 raw5782; decide +kernel
    rw [heq]
    exact (canonical5782 hH).trans (sound1040 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2442 (3 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2442 (3 : Fin 4) = raw5783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2442 raw5783; decide +kernel
    rw [heq]
    exact (canonical5783 hH).trans (sound1044 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2442 + (injectiveMoment H (mergeFirst pivotMatrix2442 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2442 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2442 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2442 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2442, value1040, value1043, value1044, value845, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2443 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2443 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2443 = Sparse.eval value2443 (momentVector H) := by
  have heq : pivotMatrix2443 = (fun u v => node2443 (pivotPermutation2443 u) v) := by apply Matrix.ext; unfold pivotMatrix2443 node2443 pivotPermutation2443; decide +kernel
  have hmoment : injectiveMoment H node2443 = injectiveMoment H pivotMatrix2443 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2443 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2443 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2443 (0 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2443 (0 : Fin 4) = raw5709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2443 raw5709; decide +kernel
    rw [heq]
    exact (canonical5709 hH).trans (sound1203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2443 (1 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2443 (1 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2443 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2443 (2 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2443 (2 : Fin 4) = raw5783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2443 raw5783; decide +kernel
    rw [heq]
    exact (canonical5783 hH).trans (sound1044 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2443 (3 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2443 (3 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2443 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2443 + (injectiveMoment H (mergeFirst pivotMatrix2443 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2443 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2443 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2443 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2443, value1044, value1110, value1203, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2444 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2444 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2444 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2444 = Sparse.eval value2444 (momentVector H) := by
  have heq : pivotMatrix2444 = (fun u v => node2444 (pivotPermutation2444 u) v) := by apply Matrix.ext; unfold pivotMatrix2444 node2444 pivotPermutation2444; decide +kernel
  have hmoment : injectiveMoment H node2444 = injectiveMoment H pivotMatrix2444 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2444 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2444 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2444 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2444 (0 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2444 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2444 (1 : Fin 4)) =
      Sparse.eval value847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2444 (1 : Fin 4) = raw5779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2444 raw5779; decide +kernel
    rw [heq]
    exact (canonical5779 hH).trans (sound847 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2444 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2444 (2 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2444 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2444 (3 : Fin 4)) =
      Sparse.eval value850 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2444 (3 : Fin 4) = raw5785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2444 raw5785; decide +kernel
    rw [heq]
    exact (canonical5785 hH).trans (sound850 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2444 + (injectiveMoment H (mergeFirst pivotMatrix2444 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2444 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2444 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2444 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2444, value1063, value1110, value847, value850, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2445 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2445 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2445 = Sparse.eval value2445 (momentVector H) := by
  have heq : pivotMatrix2445 = (fun u v => node2445 (pivotPermutation2445 u) v) := by apply Matrix.ext; unfold pivotMatrix2445 node2445 pivotPermutation2445; decide +kernel
  have hmoment : injectiveMoment H node2445 = injectiveMoment H pivotMatrix2445 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2445 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2445 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2445 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2445 (0 : Fin 4) = raw5714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2445 raw5714; decide +kernel
    rw [heq]
    exact (canonical5714 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2445 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2445 (1 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2445 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2445 (2 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2445 (2 : Fin 4) = raw5788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2445 raw5788; decide +kernel
    rw [heq]
    exact (canonical5788 hH).trans (sound1039 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2445 (3 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2445 (3 : Fin 4) = raw5789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2445 raw5789; decide +kernel
    rw [heq]
    exact (canonical5789 hH).trans (sound838 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2445 + (injectiveMoment H (mergeFirst pivotMatrix2445 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2445 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2445 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2445 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2445, value1039, value1110, value1202, value838, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2446 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem sound2446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2446 = Sparse.eval value2446 (momentVector H) := by
  have heq : pivotMatrix2446 = (fun u v => node2446 (pivotPermutation2446 u) v) := by apply Matrix.ext; unfold pivotMatrix2446 node2446 pivotPermutation2446; decide +kernel
  have hmoment : injectiveMoment H node2446 = injectiveMoment H pivotMatrix2446 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2446 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2446 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2446 (0 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2446 (0 : Fin 4) = raw5834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2446 raw5834; decide +kernel
    rw [heq]
    exact (canonical5834 hH).trans (sound1109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2446 (1 : Fin 4)) =
      Sparse.eval value843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2446 (1 : Fin 4) = raw5772 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2446 raw5772; decide +kernel
    rw [heq]
    exact (canonical5772 hH).trans (sound843 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2446 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2446 (2 : Fin 4) = raw5768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2446 raw5768; decide +kernel
    rw [heq]
    exact (canonical5768 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2446 (3 : Fin 4)) =
      Sparse.eval value839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2446 (3 : Fin 4) = raw5767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2446 raw5767; decide +kernel
    rw [heq]
    exact (canonical5767 hH).trans (sound839 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2446 + (injectiveMoment H (mergeFirst pivotMatrix2446 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2446 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2446 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2446 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2446, value1053, value1109, value839, value843, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2447 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2447 = Sparse.eval value2447 (momentVector H) := by
  have heq : pivotMatrix2447 = (fun u v => node2447 (pivotPermutation2447 u) v) := by apply Matrix.ext; unfold pivotMatrix2447 node2447 pivotPermutation2447; decide +kernel
  have hmoment : injectiveMoment H node2447 = injectiveMoment H pivotMatrix2447 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2447 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2447 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2447 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (0 : Fin 4) = raw5836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5836; decide +kernel
    rw [heq]
    exact (canonical5836 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2447 (1 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (1 : Fin 4) = raw5783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5783; decide +kernel
    rw [heq]
    exact (canonical5783 hH).trans (sound1044 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2447 (2 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (2 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2447 (3 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2447 (3 : Fin 4) = raw5777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2447 raw5777; decide +kernel
    rw [heq]
    exact (canonical5777 hH).trans (sound845 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2447 + (injectiveMoment H (mergeFirst pivotMatrix2447 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2447 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2447 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2447 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2447, value1044, value1110, value845, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2448 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2448 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2448 = Sparse.eval value2448 (momentVector H) := by
  have heq : pivotMatrix2448 = (fun u v => node2448 (pivotPermutation2448 u) v) := by apply Matrix.ext; unfold pivotMatrix2448 node2448 pivotPermutation2448; decide +kernel
  have hmoment : injectiveMoment H node2448 = injectiveMoment H pivotMatrix2448 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2448 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2448 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2448 (0 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2448 (0 : Fin 4) = raw5838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2448 raw5838; decide +kernel
    rw [heq]
    exact (canonical5838 hH).trans (sound1039 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2448 (1 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2448 (1 : Fin 4) = raw5787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2448 raw5787; decide +kernel
    rw [heq]
    exact (canonical5787 hH).trans (sound1044 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2448 (2 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2448 (2 : Fin 4) = raw5783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2448 raw5783; decide +kernel
    rw [heq]
    exact (canonical5783 hH).trans (sound1044 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2448 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2448 (3 : Fin 4) = raw5782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2448 raw5782; decide +kernel
    rw [heq]
    exact (canonical5782 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2448 + (injectiveMoment H (mergeFirst pivotMatrix2448 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2448 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2448 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2448 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2448, value1039, value1040, value1044, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2449 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2449 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2449 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2449 = Sparse.eval value2449 (momentVector H) := by
  have heq : pivotMatrix2449 = (fun u v => node2449 (pivotPermutation2449 u) v) := by apply Matrix.ext; unfold pivotMatrix2449 node2449 pivotPermutation2449; decide +kernel
  have hmoment : injectiveMoment H node2449 = injectiveMoment H pivotMatrix2449 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2449 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2449 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2449 (0 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2449 (0 : Fin 4) = raw5839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2449 raw5839; decide +kernel
    rw [heq]
    exact (canonical5839 hH).trans (sound1044 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2449 (1 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2449 (1 : Fin 4) = raw5788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2449 raw5788; decide +kernel
    rw [heq]
    exact (canonical5788 hH).trans (sound1039 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2449 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2449 (2 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2449 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2449 (3 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2449 (3 : Fin 4) = raw5783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2449 raw5783; decide +kernel
    rw [heq]
    exact (canonical5783 hH).trans (sound1044 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2449 + (injectiveMoment H (mergeFirst pivotMatrix2449 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2449 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2449 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2449 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2449, value1039, value1044, value1110, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2450 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2450 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem sound2450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2450 = Sparse.eval value2450 (momentVector H) := by
  have heq : pivotMatrix2450 = (fun u v => node2450 (pivotPermutation2450 u) v) := by apply Matrix.ext; unfold pivotMatrix2450 node2450 pivotPermutation2450; decide +kernel
  have hmoment : injectiveMoment H node2450 = injectiveMoment H pivotMatrix2450 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2450 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2450 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2450 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2450 (0 : Fin 4) = raw5840 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2450 raw5840; decide +kernel
    rw [heq]
    exact (canonical5840 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2450 (1 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2450 (1 : Fin 4) = raw5792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2450 raw5792; decide +kernel
    rw [heq]
    exact (canonical5792 hH).trans (sound838 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2450 (2 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2450 (2 : Fin 4) = raw5789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2450 raw5789; decide +kernel
    rw [heq]
    exact (canonical5789 hH).trans (sound838 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2450 (3 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2450 (3 : Fin 4) = raw5788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2450 raw5788; decide +kernel
    rw [heq]
    exact (canonical5788 hH).trans (sound1039 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2450 + (injectiveMoment H (mergeFirst pivotMatrix2450 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2450 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2450 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2450 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2450, value1039, value1040, value838, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2451 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2451 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2451 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2451 = Sparse.eval value2451 (momentVector H) := by
  have heq : pivotMatrix2451 = (fun u v => node2451 (pivotPermutation2451 u) v) := by apply Matrix.ext; unfold pivotMatrix2451 node2451 pivotPermutation2451; decide +kernel
  have hmoment : injectiveMoment H node2451 = injectiveMoment H pivotMatrix2451 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2451 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2451 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2451 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2451 (0 : Fin 4) = raw6498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2451 raw6498; decide +kernel
    rw [heq]
    exact (canonical6498 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2451 (1 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2451 (1 : Fin 4) = raw5791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2451 raw5791; decide +kernel
    rw [heq]
    exact (canonical5791 hH).trans (sound846 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2451 (2 : Fin 4)) =
      Sparse.eval value843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2451 (2 : Fin 4) = raw5772 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2451 raw5772; decide +kernel
    rw [heq]
    exact (canonical5772 hH).trans (sound843 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2451 (3 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2451 (3 : Fin 4) = raw5771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2451 raw5771; decide +kernel
    rw [heq]
    exact (canonical5771 hH).trans (sound842 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2451 + (injectiveMoment H (mergeFirst pivotMatrix2451 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2451 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2451 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2451 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2451, value1053, value842, value843, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2452 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2452 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem sound2452 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2452 = Sparse.eval value2452 (momentVector H) := by
  have heq : pivotMatrix2452 = (fun u v => node2452 (pivotPermutation2452 u) v) := by apply Matrix.ext; unfold pivotMatrix2452 node2452 pivotPermutation2452; decide +kernel
  have hmoment : injectiveMoment H node2452 = injectiveMoment H pivotMatrix2452 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2452 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2452 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2452 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2452 (0 : Fin 4) = raw6681 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2452 raw6681; decide +kernel
    rw [heq]
    exact (canonical6681 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2452 (1 : Fin 4)) =
      Sparse.eval value847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2452 (1 : Fin 4) = raw5794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2452 raw5794; decide +kernel
    rw [heq]
    exact (canonical5794 hH).trans (sound847 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2452 (2 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2452 (2 : Fin 4) = raw5773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2452 raw5773; decide +kernel
    rw [heq]
    exact (canonical5773 hH).trans (sound854 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2452 (3 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2452 (3 : Fin 4) = raw5771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2452 raw5771; decide +kernel
    rw [heq]
    exact (canonical5771 hH).trans (sound842 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2452 + (injectiveMoment H (mergeFirst pivotMatrix2452 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2452 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2452 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2452 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2452, value1110, value842, value847, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2453 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2453 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2453 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2453 = Sparse.eval value2453 (momentVector H) := by
  have heq : pivotMatrix2453 = (fun u v => node2453 (pivotPermutation2453 u) v) := by apply Matrix.ext; unfold pivotMatrix2453 node2453 pivotPermutation2453; decide +kernel
  have hmoment : injectiveMoment H node2453 = injectiveMoment H pivotMatrix2453 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2453 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2453 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2453 (0 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2453 (0 : Fin 4) = raw6926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2453 raw6926; decide +kernel
    rw [heq]
    exact (canonical6926 hH).trans (sound1054 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2453 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2453 (1 : Fin 4) = raw5836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2453 raw5836; decide +kernel
    rw [heq]
    exact (canonical5836 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2453 (2 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2453 (2 : Fin 4) = raw5823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2453 raw5823; decide +kernel
    rw [heq]
    exact (canonical5823 hH).trans (sound854 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2453 (3 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2453 (3 : Fin 4) = raw5822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2453 raw5822; decide +kernel
    rw [heq]
    exact (canonical5822 hH).trans (sound853 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2453 + (injectiveMoment H (mergeFirst pivotMatrix2453 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2453 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2453 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2453 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2453, value1054, value1110, value853, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2454 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2454 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem sound2454 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2454 = Sparse.eval value2454 (momentVector H) := by
  have heq : pivotMatrix2454 = (fun u v => node2454 (pivotPermutation2454 u) v) := by apply Matrix.ext; unfold pivotMatrix2454 node2454 pivotPermutation2454; decide +kernel
  have hmoment : injectiveMoment H node2454 = injectiveMoment H pivotMatrix2454 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2454 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2454 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2454 (0 : Fin 4)) =
      Sparse.eval value1259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2454 (0 : Fin 4) = raw5752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2454 raw5752; decide +kernel
    rw [heq]
    exact (canonical5752 hH).trans (sound1259 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2454 (1 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2454 (1 : Fin 4) = raw5822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2454 raw5822; decide +kernel
    rw [heq]
    exact (canonical5822 hH).trans (sound853 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2454 (2 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2454 (2 : Fin 4) = raw5828 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2454 raw5828; decide +kernel
    rw [heq]
    exact (canonical5828 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2454 (3 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2454 (3 : Fin 4) = raw5830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2454 raw5830; decide +kernel
    rw [heq]
    exact (canonical5830 hH).trans (sound1260 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2454 + (injectiveMoment H (mergeFirst pivotMatrix2454 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2454 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2454 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2454 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2454, value1047, value1259, value1260, value853, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2455 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2455 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2455 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2455 = Sparse.eval value2455 (momentVector H) := by
  have heq : pivotMatrix2455 = (fun u v => node2455 (pivotPermutation2455 u) v) := by apply Matrix.ext; unfold pivotMatrix2455 node2455 pivotPermutation2455; decide +kernel
  have hmoment : injectiveMoment H node2455 = injectiveMoment H pivotMatrix2455 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2455 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2455 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2455 (0 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2455 (0 : Fin 4) = raw5754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2455 raw5754; decide +kernel
    rw [heq]
    exact (canonical5754 hH).trans (sound1284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2455 (1 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2455 (1 : Fin 4) = raw5823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2455 raw5823; decide +kernel
    rw [heq]
    exact (canonical5823 hH).trans (sound854 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2455 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2455 (2 : Fin 4) = raw5831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2455 raw5831; decide +kernel
    rw [heq]
    exact (canonical5831 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2455 (3 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2455 (3 : Fin 4) = raw5832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2455 raw5832; decide +kernel
    rw [heq]
    exact (canonical5832 hH).trans (sound1053 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2455 + (injectiveMoment H (mergeFirst pivotMatrix2455 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2455 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2455 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2455 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2455, value1053, value1265, value1284, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2456 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2456 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound2456 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2456 = Sparse.eval value2456 (momentVector H) := by
  have heq : pivotMatrix2456 = (fun u v => node2456 (pivotPermutation2456 u) v) := by apply Matrix.ext; unfold pivotMatrix2456 node2456 pivotPermutation2456; decide +kernel
  have hmoment : injectiveMoment H node2456 = injectiveMoment H pivotMatrix2456 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2456 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2456 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2456 (0 : Fin 5)) =
      Sparse.eval value866 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2456 (0 : Fin 5) = raw6722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2456 raw6722; decide +kernel
    rw [heq]
    exact (canonical6722 hH).trans (sound866 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2456 (1 : Fin 5)) =
      Sparse.eval value862 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2456 (1 : Fin 5) = raw5867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2456 raw5867; decide +kernel
    rw [heq]
    exact (canonical5867 hH).trans (sound862 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2456 (2 : Fin 5)) =
      Sparse.eval value857 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2456 (2 : Fin 5) = raw5855 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2456 raw5855; decide +kernel
    rw [heq]
    exact (canonical5855 hH).trans (sound857 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2456 (3 : Fin 5)) =
      Sparse.eval value855 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2456 (3 : Fin 5) = raw5853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2456 raw5853; decide +kernel
    rw [heq]
    exact (canonical5853 hH).trans (sound855 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2456 (4 : Fin 5)) =
      Sparse.eval value735 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2456 (4 : Fin 5) = raw5852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2456 raw5852; decide +kernel
    rw [heq]
    exact (canonical5852 hH).trans (sound735 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2456 + (injectiveMoment H (mergeFirst pivotMatrix2456 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2456 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2456 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2456 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2456 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2456, value735, value855, value857, value862, value866, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2457 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound2457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2457 = Sparse.eval value2457 (momentVector H) := by
  have heq : pivotMatrix2457 = (fun u v => node2457 (pivotPermutation2457 u) v) := by apply Matrix.ext; unfold pivotMatrix2457 node2457 pivotPermutation2457; decide +kernel
  have hmoment : injectiveMoment H node2457 = injectiveMoment H pivotMatrix2457 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2457 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2457 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2457 (0 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2457 (0 : Fin 5) = raw6728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2457 raw6728; decide +kernel
    rw [heq]
    exact (canonical6728 hH).trans (sound1132 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2457 (1 : Fin 5)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2457 (1 : Fin 5) = raw5870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2457 raw5870; decide +kernel
    rw [heq]
    exact (canonical5870 hH).trans (sound864 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2457 (2 : Fin 5)) =
      Sparse.eval value861 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2457 (2 : Fin 5) = raw5861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2457 raw5861; decide +kernel
    rw [heq]
    exact (canonical5861 hH).trans (sound861 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2457 (3 : Fin 5)) =
      Sparse.eval value860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2457 (3 : Fin 5) = raw5859 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2457 raw5859; decide +kernel
    rw [heq]
    exact (canonical5859 hH).trans (sound860 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2457 (4 : Fin 5)) =
      Sparse.eval value859 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2457 (4 : Fin 5) = raw5858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2457 raw5858; decide +kernel
    rw [heq]
    exact (canonical5858 hH).trans (sound859 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2457 + (injectiveMoment H (mergeFirst pivotMatrix2457 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2457 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2457 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2457 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2457 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2457, value1132, value859, value860, value861, value864, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2458 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem sound2458 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2458 = Sparse.eval value2458 (momentVector H) := by
  have heq : pivotMatrix2458 = (fun u v => node2458 (pivotPermutation2458 u) v) := by apply Matrix.ext; unfold pivotMatrix2458 node2458 pivotPermutation2458; decide +kernel
  have hmoment : injectiveMoment H node2458 = injectiveMoment H pivotMatrix2458 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2458 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2458 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2458 (0 : Fin 5)) =
      Sparse.eval value432 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2458 (0 : Fin 5) = raw1370 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2458 raw1370; decide +kernel
    rw [heq]
    exact (canonical1370 hH).trans (sound432 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2458 (1 : Fin 5)) =
      Sparse.eval value855 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2458 (1 : Fin 5) = raw5853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2458 raw5853; decide +kernel
    rw [heq]
    exact (canonical5853 hH).trans (sound855 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2458 (2 : Fin 5)) =
      Sparse.eval value862 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2458 (2 : Fin 5) = raw5917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2458 raw5917; decide +kernel
    rw [heq]
    exact (canonical5917 hH).trans (sound862 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2458 (3 : Fin 5)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2458 (3 : Fin 5) = raw5926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2458 raw5926; decide +kernel
    rw [heq]
    exact (canonical5926 hH).trans (sound267 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2458 (4 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2458 (4 : Fin 5) = raw5931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2458 raw5931; decide +kernel
    rw [heq]
    exact (canonical5931 hH).trans (sound882 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2458 + (injectiveMoment H (mergeFirst pivotMatrix2458 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2458 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2458 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2458 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2458 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2458, value267, value432, value855, value862, value882, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2459 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem sound2459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2459 = Sparse.eval value2459 (momentVector H) := by
  have heq : pivotMatrix2459 = (fun u v => node2459 (pivotPermutation2459 u) v) := by apply Matrix.ext; unfold pivotMatrix2459 node2459 pivotPermutation2459; decide +kernel
  have hmoment : injectiveMoment H node2459 = injectiveMoment H pivotMatrix2459 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2459 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2459 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2459 (0 : Fin 5)) =
      Sparse.eval value433 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2459 (0 : Fin 5) = raw1371 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2459 raw1371; decide +kernel
    rw [heq]
    exact (canonical1371 hH).trans (sound433 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2459 (1 : Fin 5)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2459 (1 : Fin 5) = raw5854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2459 raw5854; decide +kernel
    rw [heq]
    exact (canonical5854 hH).trans (sound856 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2459 (2 : Fin 5)) =
      Sparse.eval value866 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2459 (2 : Fin 5) = raw5918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2459 raw5918; decide +kernel
    rw [heq]
    exact (canonical5918 hH).trans (sound866 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2459 (3 : Fin 5)) =
      Sparse.eval value881 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2459 (3 : Fin 5) = raw5927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2459 raw5927; decide +kernel
    rw [heq]
    exact (canonical5927 hH).trans (sound881 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2459 (4 : Fin 5)) =
      Sparse.eval value881 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2459 (4 : Fin 5) = raw5932 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2459 raw5932; decide +kernel
    rw [heq]
    exact (canonical5932 hH).trans (sound881 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2459 + (injectiveMoment H (mergeFirst pivotMatrix2459 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2459 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2459 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2459 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2459 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2459, value433, value856, value866, value881, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2460 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound2460 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2460 = Sparse.eval value2460 (momentVector H) := by
  have heq : pivotMatrix2460 = (fun u v => node2460 (pivotPermutation2460 u) v) := by apply Matrix.ext; unfold pivotMatrix2460 node2460 pivotPermutation2460; decide +kernel
  have hmoment : injectiveMoment H node2460 = injectiveMoment H pivotMatrix2460 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2460 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2460 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2460 (0 : Fin 5)) =
      Sparse.eval value434 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2460 (0 : Fin 5) = raw1372 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2460 raw1372; decide +kernel
    rw [heq]
    exact (canonical1372 hH).trans (sound434 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2460 (1 : Fin 5)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2460 (1 : Fin 5) = raw5856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2460 raw5856; decide +kernel
    rw [heq]
    exact (canonical5856 hH).trans (sound858 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2460 (2 : Fin 5)) =
      Sparse.eval value870 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2460 (2 : Fin 5) = raw5920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2460 raw5920; decide +kernel
    rw [heq]
    exact (canonical5920 hH).trans (sound870 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2460 (3 : Fin 5)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2460 (3 : Fin 5) = raw5934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2460 raw5934; decide +kernel
    rw [heq]
    exact (canonical5934 hH).trans (sound268 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2460 (4 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2460 (4 : Fin 5) = raw5936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2460 raw5936; decide +kernel
    rw [heq]
    exact (canonical5936 hH).trans (sound882 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2460 + (injectiveMoment H (mergeFirst pivotMatrix2460 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2460 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2460 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2460 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2460 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2460, value268, value434, value858, value870, value882, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2461 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound2461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2461 = Sparse.eval value2461 (momentVector H) := by
  have heq : pivotMatrix2461 = (fun u v => node2461 (pivotPermutation2461 u) v) := by apply Matrix.ext; unfold pivotMatrix2461 node2461 pivotPermutation2461; decide +kernel
  have hmoment : injectiveMoment H node2461 = injectiveMoment H pivotMatrix2461 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2461 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2461 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2461 (0 : Fin 5)) =
      Sparse.eval value435 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2461 (0 : Fin 5) = raw1373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2461 raw1373; decide +kernel
    rw [heq]
    exact (canonical1373 hH).trans (sound435 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2461 (1 : Fin 5)) =
      Sparse.eval value860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2461 (1 : Fin 5) = raw5859 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2461 raw5859; decide +kernel
    rw [heq]
    exact (canonical5859 hH).trans (sound860 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2461 (2 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2461 (2 : Fin 5) = raw5921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2461 raw5921; decide +kernel
    rw [heq]
    exact (canonical5921 hH).trans (sound876 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2461 (3 : Fin 5)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2461 (3 : Fin 5) = raw5938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2461 raw5938; decide +kernel
    rw [heq]
    exact (canonical5938 hH).trans (sound269 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2461 (4 : Fin 5)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2461 (4 : Fin 5) = raw5941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2461 raw5941; decide +kernel
    rw [heq]
    exact (canonical5941 hH).trans (sound269 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2461 + (injectiveMoment H (mergeFirst pivotMatrix2461 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2461 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2461 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2461 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2461 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2461, value269, value435, value860, value876, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2462 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2462 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2462 = Sparse.eval value2462 (momentVector H) := by
  have heq : pivotMatrix2462 = (fun u v => node2462 (pivotPermutation2462 u) v) := by apply Matrix.ext; unfold pivotMatrix2462 node2462 pivotPermutation2462; decide +kernel
  have hmoment : injectiveMoment H node2462 = injectiveMoment H pivotMatrix2462 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2462 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2462 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2462 (0 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2462 (0 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2462 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2462 (1 : Fin 5)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2462 (1 : Fin 5) = raw5873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2462 raw5873; decide +kernel
    rw [heq]
    exact (canonical5873 hH).trans (sound868 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2462 (2 : Fin 5)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2462 (2 : Fin 5) = raw5950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2462 raw5950; decide +kernel
    rw [heq]
    exact (canonical5950 hH).trans (sound868 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2462 (3 : Fin 5)) =
      Sparse.eval value881 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2462 (3 : Fin 5) = raw5957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2462 raw5957; decide +kernel
    rw [heq]
    exact (canonical5957 hH).trans (sound881 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2462 (4 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2462 (4 : Fin 5) = raw5961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2462 raw5961; decide +kernel
    rw [heq]
    exact (canonical5961 hH).trans (sound884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2462 + (injectiveMoment H (mergeFirst pivotMatrix2462 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2462 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2462 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2462 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2462 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2462, value440, value868, value881, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2463 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2463 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2463 = Sparse.eval value2463 (momentVector H) := by
  have heq : pivotMatrix2463 = (fun u v => node2463 (pivotPermutation2463 u) v) := by apply Matrix.ext; unfold pivotMatrix2463 node2463 pivotPermutation2463; decide +kernel
  have hmoment : injectiveMoment H node2463 = injectiveMoment H pivotMatrix2463 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2463 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2463 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2463 (0 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2463 (0 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2463 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2463 (1 : Fin 5)) =
      Sparse.eval value869 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2463 (1 : Fin 5) = raw5875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2463 raw5875; decide +kernel
    rw [heq]
    exact (canonical5875 hH).trans (sound869 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2463 (2 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2463 (2 : Fin 5) = raw5951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2463 raw5951; decide +kernel
    rw [heq]
    exact (canonical5951 hH).trans (sound872 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2463 (3 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2463 (3 : Fin 5) = raw5963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2463 raw5963; decide +kernel
    rw [heq]
    exact (canonical5963 hH).trans (sound882 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2463 (4 : Fin 5)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2463 (4 : Fin 5) = raw5966 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2463 raw5966; decide +kernel
    rw [heq]
    exact (canonical5966 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2463 + (injectiveMoment H (mergeFirst pivotMatrix2463 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2463 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2463 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2463 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2463 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2463, value272, value443, value869, value872, value882, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2464 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem sound2464 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2464 = Sparse.eval value2464 (momentVector H) := by
  have heq : pivotMatrix2464 = (fun u v => node2464 (pivotPermutation2464 u) v) := by apply Matrix.ext; unfold pivotMatrix2464 node2464 pivotPermutation2464; decide +kernel
  have hmoment : injectiveMoment H node2464 = injectiveMoment H pivotMatrix2464 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2464 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2464 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2464 (0 : Fin 5)) =
      Sparse.eval value445 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2464 (0 : Fin 5) = raw1411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2464 raw1411; decide +kernel
    rw [heq]
    exact (canonical1411 hH).trans (sound445 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2464 (1 : Fin 5)) =
      Sparse.eval value1287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2464 (1 : Fin 5) = raw5876 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2464 raw5876; decide +kernel
    rw [heq]
    exact (canonical5876 hH).trans (sound1287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2464 (2 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2464 (2 : Fin 5) = raw5952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2464 raw5952; decide +kernel
    rw [heq]
    exact (canonical5952 hH).trans (sound876 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2464 (3 : Fin 5)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2464 (3 : Fin 5) = raw5967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2464 raw5967; decide +kernel
    rw [heq]
    exact (canonical5967 hH).trans (sound883 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2464 (4 : Fin 5)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2464 (4 : Fin 5) = raw5969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2464 raw5969; decide +kernel
    rw [heq]
    exact (canonical5969 hH).trans (sound883 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2464 + (injectiveMoment H (mergeFirst pivotMatrix2464 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2464 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2464 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2464 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2464 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2464, value1287, value445, value876, value883, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2465 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound2465 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2465 = Sparse.eval value2465 (momentVector H) := by
  have heq : pivotMatrix2465 = (fun u v => node2465 (pivotPermutation2465 u) v) := by apply Matrix.ext; unfold pivotMatrix2465 node2465 pivotPermutation2465; decide +kernel
  have hmoment : injectiveMoment H node2465 = injectiveMoment H pivotMatrix2465 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2465 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2465 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2465 (0 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2465 (0 : Fin 5) = raw2747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2465 raw2747; decide +kernel
    rw [heq]
    exact (canonical2747 hH).trans (sound559 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2465 (1 : Fin 5)) =
      Sparse.eval value862 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2465 (1 : Fin 5) = raw5867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2465 raw5867; decide +kernel
    rw [heq]
    exact (canonical5867 hH).trans (sound862 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2465 (2 : Fin 5)) =
      Sparse.eval value867 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2465 (2 : Fin 5) = raw5919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2465 raw5919; decide +kernel
    rw [heq]
    exact (canonical5919 hH).trans (sound867 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2465 (3 : Fin 5)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2465 (3 : Fin 5) = raw5926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2465 raw5926; decide +kernel
    rw [heq]
    exact (canonical5926 hH).trans (sound267 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2465 (4 : Fin 5)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2465 (4 : Fin 5) = raw5930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2465 raw5930; decide +kernel
    rw [heq]
    exact (canonical5930 hH).trans (sound883 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2465 + (injectiveMoment H (mergeFirst pivotMatrix2465 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2465 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2465 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2465 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2465 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2465, value267, value559, value862, value867, value883, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2466 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound2466 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2466 = Sparse.eval value2466 (momentVector H) := by
  have heq : pivotMatrix2466 = (fun u v => node2466 (pivotPermutation2466 u) v) := by apply Matrix.ext; unfold pivotMatrix2466 node2466 pivotPermutation2466; decide +kernel
  have hmoment : injectiveMoment H node2466 = injectiveMoment H pivotMatrix2466 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2466 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2466 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2466 (0 : Fin 5)) =
      Sparse.eval value560 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2466 (0 : Fin 5) = raw2748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2466 raw2748; decide +kernel
    rw [heq]
    exact (canonical2748 hH).trans (sound560 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2466 (1 : Fin 5)) =
      Sparse.eval value560 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2466 (1 : Fin 5) = raw5868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2466 raw5868; decide +kernel
    rw [heq]
    exact (canonical5868 hH).trans (sound560 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2466 (2 : Fin 5)) =
      Sparse.eval value870 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2466 (2 : Fin 5) = raw5920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2466 raw5920; decide +kernel
    rw [heq]
    exact (canonical5920 hH).trans (sound870 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2466 (3 : Fin 5)) =
      Sparse.eval value881 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2466 (3 : Fin 5) = raw5927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2466 raw5927; decide +kernel
    rw [heq]
    exact (canonical5927 hH).trans (sound881 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2466 (4 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2466 (4 : Fin 5) = raw5931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2466 raw5931; decide +kernel
    rw [heq]
    exact (canonical5931 hH).trans (sound882 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2466 + (injectiveMoment H (mergeFirst pivotMatrix2466 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2466 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2466 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2466 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2466 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2466, value560, value870, value881, value882, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2467 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2467 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2467 = Sparse.eval value2467 (momentVector H) := by
  have heq : pivotMatrix2467 = (fun u v => node2467 (pivotPermutation2467 u) v) := by apply Matrix.ext; unfold pivotMatrix2467 node2467 pivotPermutation2467; decide +kernel
  have hmoment : injectiveMoment H node2467 = injectiveMoment H pivotMatrix2467 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2467 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2467 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2467 (0 : Fin 5)) =
      Sparse.eval value562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2467 (0 : Fin 5) = raw2754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2467 raw2754; decide +kernel
    rw [heq]
    exact (canonical2754 hH).trans (sound562 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2467 (1 : Fin 5)) =
      Sparse.eval value555 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2467 (1 : Fin 5) = raw5869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2467 raw5869; decide +kernel
    rw [heq]
    exact (canonical5869 hH).trans (sound555 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2467 (2 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2467 (2 : Fin 5) = raw5921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2467 raw5921; decide +kernel
    rw [heq]
    exact (canonical5921 hH).trans (sound876 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2467 (3 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2467 (3 : Fin 5) = raw5935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2467 raw5935; decide +kernel
    rw [heq]
    exact (canonical5935 hH).trans (sound882 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2467 (4 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2467 (4 : Fin 5) = raw5936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2467 raw5936; decide +kernel
    rw [heq]
    exact (canonical5936 hH).trans (sound882 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2467 + (injectiveMoment H (mergeFirst pivotMatrix2467 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2467 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2467 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2467 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2467 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2467, value555, value562, value876, value882, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2468 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound2468 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2468 = Sparse.eval value2468 (momentVector H) := by
  have heq : pivotMatrix2468 = (fun u v => node2468 (pivotPermutation2468 u) v) := by apply Matrix.ext; unfold pivotMatrix2468 node2468 pivotPermutation2468; decide +kernel
  have hmoment : injectiveMoment H node2468 = injectiveMoment H pivotMatrix2468 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2468 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2468 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2468 (0 : Fin 5)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2468 (0 : Fin 5) = raw2757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2468 raw2757; decide +kernel
    rw [heq]
    exact (canonical2757 hH).trans (sound563 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2468 (1 : Fin 5)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2468 (1 : Fin 5) = raw5870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2468 raw5870; decide +kernel
    rw [heq]
    exact (canonical5870 hH).trans (sound864 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2468 (2 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2468 (2 : Fin 5) = raw5922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2468 raw5922; decide +kernel
    rw [heq]
    exact (canonical5922 hH).trans (sound744 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2468 (3 : Fin 5)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2468 (3 : Fin 5) = raw5938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2468 raw5938; decide +kernel
    rw [heq]
    exact (canonical5938 hH).trans (sound269 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2468 (4 : Fin 5)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2468 (4 : Fin 5) = raw5939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2468 raw5939; decide +kernel
    rw [heq]
    exact (canonical5939 hH).trans (sound883 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2468 + (injectiveMoment H (mergeFirst pivotMatrix2468 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2468 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2468 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2468 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2468 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2468, value269, value563, value744, value864, value883, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2469 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2469 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2469 = Sparse.eval value2469 (momentVector H) := by
  have heq : pivotMatrix2469 = (fun u v => node2469 (pivotPermutation2469 u) v) := by apply Matrix.ext; unfold pivotMatrix2469 node2469 pivotPermutation2469; decide +kernel
  have hmoment : injectiveMoment H node2469 = injectiveMoment H pivotMatrix2469 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2469 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2469 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2469 (0 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2469 (0 : Fin 5) = raw2800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2469 raw2800; decide +kernel
    rw [heq]
    exact (canonical2800 hH).trans (sound570 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2469 (1 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2469 (1 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2469 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2469 (2 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2469 (2 : Fin 5) = raw5951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2469 raw5951; decide +kernel
    rw [heq]
    exact (canonical5951 hH).trans (sound872 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2469 (3 : Fin 5)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2469 (3 : Fin 5) = raw5958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2469 raw5958; decide +kernel
    rw [heq]
    exact (canonical5958 hH).trans (sound271 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2469 (4 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2469 (4 : Fin 5) = raw5961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2469 raw5961; decide +kernel
    rw [heq]
    exact (canonical5961 hH).trans (sound884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2469 + (injectiveMoment H (mergeFirst pivotMatrix2469 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2469 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2469 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2469 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2469 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2469, value271, value570, value872, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2470 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2470 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2470 = Sparse.eval value2470 (momentVector H) := by
  have heq : pivotMatrix2470 = (fun u v => node2470 (pivotPermutation2470 u) v) := by apply Matrix.ext; unfold pivotMatrix2470 node2470 pivotPermutation2470; decide +kernel
  have hmoment : injectiveMoment H node2470 = injectiveMoment H pivotMatrix2470 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2470 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2470 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2470 (0 : Fin 5)) =
      Sparse.eval value741 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2470 (0 : Fin 5) = raw5494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2470 raw5494; decide +kernel
    rw [heq]
    exact (canonical5494 hH).trans (sound741 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2470 (1 : Fin 5)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2470 (1 : Fin 5) = raw5873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2470 raw5873; decide +kernel
    rw [heq]
    exact (canonical5873 hH).trans (sound868 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2470 (2 : Fin 5)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2470 (2 : Fin 5) = raw5879 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2470 raw5879; decide +kernel
    rw [heq]
    exact (canonical5879 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2470 (3 : Fin 5)) =
      Sparse.eval value871 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2470 (3 : Fin 5) = raw5881 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2470 raw5881; decide +kernel
    rw [heq]
    exact (canonical5881 hH).trans (sound871 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2470 (4 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2470 (4 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2470 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2470 + (injectiveMoment H (mergeFirst pivotMatrix2470 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2470 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2470 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2470 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2470 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2470, value261, value741, value868, value871, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2471 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2471 = Sparse.eval value2471 (momentVector H) := by
  have heq : pivotMatrix2471 = (fun u v => node2471 (pivotPermutation2471 u) v) := by apply Matrix.ext; unfold pivotMatrix2471 node2471 pivotPermutation2471; decide +kernel
  have hmoment : injectiveMoment H node2471 = injectiveMoment H pivotMatrix2471 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2471 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2471 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2471 (0 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2471 (0 : Fin 5) = raw5495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2471 raw5495; decide +kernel
    rw [heq]
    exact (canonical5495 hH).trans (sound742 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2471 (1 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2471 (1 : Fin 5) = raw5874 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2471 raw5874; decide +kernel
    rw [heq]
    exact (canonical5874 hH).trans (sound570 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2471 (2 : Fin 5)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2471 (2 : Fin 5) = raw5880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2471 raw5880; decide +kernel
    rw [heq]
    exact (canonical5880 hH).trans (sound176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2471 (3 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2471 (3 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2471 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2471 (4 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2471 (4 : Fin 5) = raw5883 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2471 raw5883; decide +kernel
    rw [heq]
    exact (canonical5883 hH).trans (sound872 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2471 + (injectiveMoment H (mergeFirst pivotMatrix2471 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2471 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2471 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2471 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2471 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2471, value176, value570, value742, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2472 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2472 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2472 = Sparse.eval value2472 (momentVector H) := by
  have heq : pivotMatrix2472 = (fun u v => node2472 (pivotPermutation2472 u) v) := by apply Matrix.ext; unfold pivotMatrix2472 node2472 pivotPermutation2472; decide +kernel
  have hmoment : injectiveMoment H node2472 = injectiveMoment H pivotMatrix2472 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2472 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2472 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2472 (0 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2472 (0 : Fin 5) = raw5496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2472 raw5496; decide +kernel
    rw [heq]
    exact (canonical5496 hH).trans (sound743 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2472 (1 : Fin 5)) =
      Sparse.eval value869 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2472 (1 : Fin 5) = raw5875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2472 raw5875; decide +kernel
    rw [heq]
    exact (canonical5875 hH).trans (sound869 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2472 (2 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2472 (2 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2472 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2472 (3 : Fin 5)) =
      Sparse.eval value873 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2472 (3 : Fin 5) = raw5884 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2472 raw5884; decide +kernel
    rw [heq]
    exact (canonical5884 hH).trans (sound873 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2472 (4 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2472 (4 : Fin 5) = raw5885 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2472 raw5885; decide +kernel
    rw [heq]
    exact (canonical5885 hH).trans (sound1143 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2472 + (injectiveMoment H (mergeFirst pivotMatrix2472 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2472 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2472 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2472 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2472 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2472, value1143, value743, value869, value872, value873, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2473 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2473 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2473 = Sparse.eval value2473 (momentVector H) := by
  have heq : pivotMatrix2473 = (fun u v => node2473 (pivotPermutation2473 u) v) := by apply Matrix.ext; unfold pivotMatrix2473 node2473 pivotPermutation2473; decide +kernel
  have hmoment : injectiveMoment H node2473 = injectiveMoment H pivotMatrix2473 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2473 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2473 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2473 (0 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2473 (0 : Fin 5) = raw6758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2473 raw6758; decide +kernel
    rw [heq]
    exact (canonical6758 hH).trans (sound1143 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2473 (1 : Fin 5)) =
      Sparse.eval value877 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2473 (1 : Fin 5) = raw5903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2473 raw5903; decide +kernel
    rw [heq]
    exact (canonical5903 hH).trans (sound877 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2473 (2 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2473 (2 : Fin 5) = raw5895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2473 raw5895; decide +kernel
    rw [heq]
    exact (canonical5895 hH).trans (sound876 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2473 (3 : Fin 5)) =
      Sparse.eval value874 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2473 (3 : Fin 5) = raw5893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2473 raw5893; decide +kernel
    rw [heq]
    exact (canonical5893 hH).trans (sound874 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2473 (4 : Fin 5)) =
      Sparse.eval value874 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2473 (4 : Fin 5) = raw5892 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2473 raw5892; decide +kernel
    rw [heq]
    exact (canonical5892 hH).trans (sound874 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2473 + (injectiveMoment H (mergeFirst pivotMatrix2473 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2473 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2473 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2473 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2473 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2473, value1143, value874, value876, value877, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2474 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2474 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2474 = Sparse.eval value2474 (momentVector H) := by
  have heq : pivotMatrix2474 = (fun u v => node2474 (pivotPermutation2474 u) v) := by apply Matrix.ext; unfold pivotMatrix2474 node2474 pivotPermutation2474; decide +kernel
  have hmoment : injectiveMoment H node2474 = injectiveMoment H pivotMatrix2474 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2474 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2474 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2474 (0 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2474 (0 : Fin 5) = raw5503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2474 raw5503; decide +kernel
    rw [heq]
    exact (canonical5503 hH).trans (sound744 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2474 (1 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2474 (1 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2474 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2474 (2 : Fin 5)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2474 (2 : Fin 5) = raw5896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2474 raw5896; decide +kernel
    rw [heq]
    exact (canonical5896 hH).trans (sound263 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2474 (3 : Fin 5)) =
      Sparse.eval value875 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2474 (3 : Fin 5) = raw5897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2474 raw5897; decide +kernel
    rw [heq]
    exact (canonical5897 hH).trans (sound875 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2474 (4 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2474 (4 : Fin 5) = raw5898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2474 raw5898; decide +kernel
    rw [heq]
    exact (canonical5898 hH).trans (sound876 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2474 + (injectiveMoment H (mergeFirst pivotMatrix2474 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2474 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2474 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2474 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2474 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2474, value263, value744, value872, value875, value876, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2475 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2475 = Sparse.eval value2475 (momentVector H) := by
  have heq : pivotMatrix2475 = (fun u v => node2475 (pivotPermutation2475 u) v) := by apply Matrix.ext; unfold pivotMatrix2475 node2475 pivotPermutation2475; decide +kernel
  have hmoment : injectiveMoment H node2475 = injectiveMoment H pivotMatrix2475 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2475 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2475 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2475 (0 : Fin 5)) =
      Sparse.eval value745 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (0 : Fin 5) = raw5508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5508; decide +kernel
    rw [heq]
    exact (canonical5508 hH).trans (sound745 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2475 (1 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (1 : Fin 5) = raw5895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5895; decide +kernel
    rw [heq]
    exact (canonical5895 hH).trans (sound876 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2475 (2 : Fin 5)) =
      Sparse.eval value877 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (2 : Fin 5) = raw5903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5903; decide +kernel
    rw [heq]
    exact (canonical5903 hH).trans (sound877 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2475 (3 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (3 : Fin 5) = raw5905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5905; decide +kernel
    rw [heq]
    exact (canonical5905 hH).trans (sound744 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2475 (4 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (4 : Fin 5) = raw5906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5906; decide +kernel
    rw [heq]
    exact (canonical5906 hH).trans (sound744 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2475 + (injectiveMoment H (mergeFirst pivotMatrix2475 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2475, value744, value745, value876, value877, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2476 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

theorem sound2476 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2476 = Sparse.eval value2476 (momentVector H) := by
  have heq : pivotMatrix2476 = (fun u v => node2476 (pivotPermutation2476 u) v) := by apply Matrix.ext; unfold pivotMatrix2476 node2476 pivotPermutation2476; decide +kernel
  have hmoment : injectiveMoment H node2476 = injectiveMoment H pivotMatrix2476 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2476 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2476 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2476 (0 : Fin 5)) =
      Sparse.eval value746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2476 (0 : Fin 5) = raw5512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2476 raw5512; decide +kernel
    rw [heq]
    exact (canonical5512 hH).trans (sound746 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2476 (1 : Fin 5)) =
      Sparse.eval value878 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2476 (1 : Fin 5) = raw5910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2476 raw5910; decide +kernel
    rw [heq]
    exact (canonical5910 hH).trans (sound878 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2476 (2 : Fin 5)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2476 (2 : Fin 5) = raw5924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2476 raw5924; decide +kernel
    rw [heq]
    exact (canonical5924 hH).trans (sound267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2476 (3 : Fin 5)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2476 (3 : Fin 5) = raw5926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2476 raw5926; decide +kernel
    rw [heq]
    exact (canonical5926 hH).trans (sound267 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2476 (4 : Fin 5)) =
      Sparse.eval value881 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2476 (4 : Fin 5) = raw5927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2476 raw5927; decide +kernel
    rw [heq]
    exact (canonical5927 hH).trans (sound881 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2476 + (injectiveMoment H (mergeFirst pivotMatrix2476 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2476 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2476 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2476 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2476 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2476, value267, value746, value878, value881, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2477 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

theorem sound2477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2477 = Sparse.eval value2477 (momentVector H) := by
  have heq : pivotMatrix2477 = (fun u v => node2477 (pivotPermutation2477 u) v) := by apply Matrix.ext; unfold pivotMatrix2477 node2477 pivotPermutation2477; decide +kernel
  have hmoment : injectiveMoment H node2477 = injectiveMoment H pivotMatrix2477 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2477 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2477 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2477 (0 : Fin 5)) =
      Sparse.eval value747 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2477 (0 : Fin 5) = raw5513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2477 raw5513; decide +kernel
    rw [heq]
    exact (canonical5513 hH).trans (sound747 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2477 (1 : Fin 5)) =
      Sparse.eval value879 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2477 (1 : Fin 5) = raw5911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2477 raw5911; decide +kernel
    rw [heq]
    exact (canonical5911 hH).trans (sound879 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2477 (2 : Fin 5)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2477 (2 : Fin 5) = raw5925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2477 raw5925; decide +kernel
    rw [heq]
    exact (canonical5925 hH).trans (sound269 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2477 (3 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2477 (3 : Fin 5) = raw5928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2477 raw5928; decide +kernel
    rw [heq]
    exact (canonical5928 hH).trans (sound882 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2477 (4 : Fin 5)) =
      Sparse.eval value883 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2477 (4 : Fin 5) = raw5929 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2477 raw5929; decide +kernel
    rw [heq]
    exact (canonical5929 hH).trans (sound883 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2477 + (injectiveMoment H (mergeFirst pivotMatrix2477 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2477 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2477 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2477 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2477 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2477, value269, value747, value879, value882, value883, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2478 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem sound2478 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2478 = Sparse.eval value2478 (momentVector H) := by
  have heq : pivotMatrix2478 = (fun u v => node2478 (pivotPermutation2478 u) v) := by apply Matrix.ext; unfold pivotMatrix2478 node2478 pivotPermutation2478; decide +kernel
  have hmoment : injectiveMoment H node2478 = injectiveMoment H pivotMatrix2478 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2478 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2478 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2478 (0 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2478 (0 : Fin 5) = raw5526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2478 raw5526; decide +kernel
    rw [heq]
    exact (canonical5526 hH).trans (sound748 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2478 (1 : Fin 5)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2478 (1 : Fin 5) = raw5944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2478 raw5944; decide +kernel
    rw [heq]
    exact (canonical5944 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2478 (2 : Fin 5)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2478 (2 : Fin 5) = raw5954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2478 raw5954; decide +kernel
    rw [heq]
    exact (canonical5954 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2478 (3 : Fin 5)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2478 (3 : Fin 5) = raw5958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2478 raw5958; decide +kernel
    rw [heq]
    exact (canonical5958 hH).trans (sound271 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2478 (4 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2478 (4 : Fin 5) = raw5959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2478 raw5959; decide +kernel
    rw [heq]
    exact (canonical5959 hH).trans (sound884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2478 + (injectiveMoment H (mergeFirst pivotMatrix2478 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2478 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2478 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2478 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2478 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2478, value271, value748, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2479 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem sound2479 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2479 = Sparse.eval value2479 (momentVector H) := by
  have heq : pivotMatrix2479 = (fun u v => node2479 (pivotPermutation2479 u) v) := by apply Matrix.ext; unfold pivotMatrix2479 node2479 pivotPermutation2479; decide +kernel
  have hmoment : injectiveMoment H node2479 = injectiveMoment H pivotMatrix2479 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2479 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2479 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2479 (0 : Fin 5)) =
      Sparse.eval value749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2479 (0 : Fin 5) = raw5527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2479 raw5527; decide +kernel
    rw [heq]
    exact (canonical5527 hH).trans (sound749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2479 (1 : Fin 5)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2479 (1 : Fin 5) = raw5945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2479 raw5945; decide +kernel
    rw [heq]
    exact (canonical5945 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2479 (2 : Fin 5)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2479 (2 : Fin 5) = raw5955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2479 raw5955; decide +kernel
    rw [heq]
    exact (canonical5955 hH).trans (sound272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2479 (3 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2479 (3 : Fin 5) = raw5959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2479 raw5959; decide +kernel
    rw [heq]
    exact (canonical5959 hH).trans (sound884 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2479 (4 : Fin 5)) =
      Sparse.eval value885 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2479 (4 : Fin 5) = raw5960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2479 raw5960; decide +kernel
    rw [heq]
    exact (canonical5960 hH).trans (sound885 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2479 + (injectiveMoment H (mergeFirst pivotMatrix2479 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2479 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2479 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2479 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2479 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2479, value272, value749, value884, value885, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2480 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem sound2480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2480 = Sparse.eval value2480 (momentVector H) := by
  have heq : pivotMatrix2480 = (fun u v => node2480 (pivotPermutation2480 u) v) := by apply Matrix.ext; unfold pivotMatrix2480 node2480 pivotPermutation2480; decide +kernel
  have hmoment : injectiveMoment H node2480 = injectiveMoment H pivotMatrix2480 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2480 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2480 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2480 (0 : Fin 5)) =
      Sparse.eval value1153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2480 (0 : Fin 5) = raw6843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2480 raw6843; decide +kernel
    rw [heq]
    exact (canonical6843 hH).trans (sound1153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2480 (1 : Fin 5)) =
      Sparse.eval value885 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2480 (1 : Fin 5) = raw5975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2480 raw5975; decide +kernel
    rw [heq]
    exact (canonical5975 hH).trans (sound885 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2480 (2 : Fin 5)) =
      Sparse.eval value885 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2480 (2 : Fin 5) = raw5964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2480 raw5964; decide +kernel
    rw [heq]
    exact (canonical5964 hH).trans (sound885 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2480 (3 : Fin 5)) =
      Sparse.eval value885 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2480 (3 : Fin 5) = raw5960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2480 raw5960; decide +kernel
    rw [heq]
    exact (canonical5960 hH).trans (sound885 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2480 (4 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2480 (4 : Fin 5) = raw5959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2480 raw5959; decide +kernel
    rw [heq]
    exact (canonical5959 hH).trans (sound884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2480 + (injectiveMoment H (mergeFirst pivotMatrix2480 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2480 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2480 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2480 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2480 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2480, value1153, value884, value885, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2481 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2481 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem sound2481 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2481 = Sparse.eval value2481 (momentVector H) := by
  have heq : pivotMatrix2481 = (fun u v => node2481 (pivotPermutation2481 u) v) := by apply Matrix.ext; unfold pivotMatrix2481 node2481 pivotPermutation2481; decide +kernel
  have hmoment : injectiveMoment H node2481 = injectiveMoment H pivotMatrix2481 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2481 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2481 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2481 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2481 (0 : Fin 4) = raw6972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2481 raw6972; decide +kernel
    rw [heq]
    exact (canonical6972 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2481 (1 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2481 (1 : Fin 4) = raw6008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2481 raw6008; decide +kernel
    rw [heq]
    exact (canonical6008 hH).trans (sound786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2481 (2 : Fin 4)) =
      Sparse.eval value398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2481 (2 : Fin 4) = raw6006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2481 raw6006; decide +kernel
    rw [heq]
    exact (canonical6006 hH).trans (sound398 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2481 (3 : Fin 4)) =
      Sparse.eval value501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2481 (3 : Fin 4) = raw6005 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2481 raw6005; decide +kernel
    rw [heq]
    exact (canonical6005 hH).trans (sound501 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2481 + (injectiveMoment H (mergeFirst pivotMatrix2481 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2481 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2481 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2481 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2481, value398, value501, value786, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2482 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2482 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound2482 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2482 = Sparse.eval value2482 (momentVector H) := by
  have heq : pivotMatrix2482 = (fun u v => node2482 (pivotPermutation2482 u) v) := by apply Matrix.ext; unfold pivotMatrix2482 node2482 pivotPermutation2482; decide +kernel
  have hmoment : injectiveMoment H node2482 = injectiveMoment H pivotMatrix2482 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2482 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2482 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2482 (0 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2482 (0 : Fin 4) = raw7042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2482 raw7042; decide +kernel
    rw [heq]
    exact (canonical7042 hH).trans (sound1013 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2482 (1 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2482 (1 : Fin 4) = raw6011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2482 raw6011; decide +kernel
    rw [heq]
    exact (canonical6011 hH).trans (sound894 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2482 (2 : Fin 4)) =
      Sparse.eval value687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2482 (2 : Fin 4) = raw6007 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2482 raw6007; decide +kernel
    rw [heq]
    exact (canonical6007 hH).trans (sound687 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2482 (3 : Fin 4)) =
      Sparse.eval value501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2482 (3 : Fin 4) = raw6005 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2482 raw6005; decide +kernel
    rw [heq]
    exact (canonical6005 hH).trans (sound501 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2482 + (injectiveMoment H (mergeFirst pivotMatrix2482 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2482 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2482 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2482 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2482, value1013, value501, value687, value894, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2483 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2483 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2483 = Sparse.eval value2483 (momentVector H) := by
  have heq : pivotMatrix2483 = (fun u v => node2483 (pivotPermutation2483 u) v) := by apply Matrix.ext; unfold pivotMatrix2483 node2483 pivotPermutation2483; decide +kernel
  have hmoment : injectiveMoment H node2483 = injectiveMoment H pivotMatrix2483 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2483 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2483 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2483 (0 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2483 (0 : Fin 4) = raw1700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2483 raw1700; decide +kernel
    rw [heq]
    exact (canonical1700 hH).trans (sound464 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2483 (1 : Fin 4)) =
      Sparse.eval value891 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2483 (1 : Fin 4) = raw6025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2483 raw6025; decide +kernel
    rw [heq]
    exact (canonical6025 hH).trans (sound891 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2483 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2483 (2 : Fin 4) = raw6106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2483 raw6106; decide +kernel
    rw [heq]
    exact (canonical6106 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2483 (3 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2483 (3 : Fin 4) = raw6109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2483 raw6109; decide +kernel
    rw [heq]
    exact (canonical6109 hH).trans (sound766 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2483 + (injectiveMoment H (mergeFirst pivotMatrix2483 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2483 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2483 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2483 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2483, value464, value766, value891, value894, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2484 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2484 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem sound2484 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2484 = Sparse.eval value2484 (momentVector H) := by
  have heq : pivotMatrix2484 = (fun u v => node2484 (pivotPermutation2484 u) v) := by apply Matrix.ext; unfold pivotMatrix2484 node2484 pivotPermutation2484; decide +kernel
  have hmoment : injectiveMoment H node2484 = injectiveMoment H pivotMatrix2484 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2484 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2484 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2484 (0 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2484 (0 : Fin 4) = raw8011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2484 raw8011; decide +kernel
    rw [heq]
    exact (canonical8011 hH).trans (sound1100 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2484 (1 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2484 (1 : Fin 4) = raw6042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2484 raw6042; decide +kernel
    rw [heq]
    exact (canonical6042 hH).trans (sound894 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2484 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2484 (2 : Fin 4) = raw6011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2484 raw6011; decide +kernel
    rw [heq]
    exact (canonical6011 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2484 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2484 (3 : Fin 4) = raw6010 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2484 raw6010; decide +kernel
    rw [heq]
    exact (canonical6010 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2484 + (injectiveMoment H (mergeFirst pivotMatrix2484 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2484 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2484 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2484 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2484, value1100, value894, value896, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2485 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2485 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2485 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2485 = Sparse.eval value2485 (momentVector H) := by
  have heq : pivotMatrix2485 = (fun u v => node2485 (pivotPermutation2485 u) v) := by apply Matrix.ext; unfold pivotMatrix2485 node2485 pivotPermutation2485; decide +kernel
  have hmoment : injectiveMoment H node2485 = injectiveMoment H pivotMatrix2485 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2485 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2485 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2485 (0 : Fin 4)) =
      Sparse.eval value1124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2485 (0 : Fin 4) = raw7051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2485 raw7051; decide +kernel
    rw [heq]
    exact (canonical7051 hH).trans (sound1124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2485 (1 : Fin 4)) =
      Sparse.eval value1121 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2485 (1 : Fin 4) = raw6026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2485 raw6026; decide +kernel
    rw [heq]
    exact (canonical6026 hH).trans (sound1121 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2485 (2 : Fin 4)) =
      Sparse.eval value899 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2485 (2 : Fin 4) = raw6016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2485 raw6016; decide +kernel
    rw [heq]
    exact (canonical6016 hH).trans (sound899 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2485 (3 : Fin 4)) =
      Sparse.eval value1125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2485 (3 : Fin 4) = raw6015 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2485 raw6015; decide +kernel
    rw [heq]
    exact (canonical6015 hH).trans (sound1125 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2485 + (injectiveMoment H (mergeFirst pivotMatrix2485 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2485 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2485 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2485 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2485, value1121, value1124, value1125, value899, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2486 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2486 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

theorem sound2486 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2486 = Sparse.eval value2486 (momentVector H) := by
  have heq : pivotMatrix2486 = (fun u v => node2486 (pivotPermutation2486 u) v) := by apply Matrix.ext; unfold pivotMatrix2486 node2486 pivotPermutation2486; decide +kernel
  have hmoment : injectiveMoment H node2486 = injectiveMoment H pivotMatrix2486 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2486 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2486 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2486 (0 : Fin 4)) =
      Sparse.eval value921 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2486 (0 : Fin 4) = raw2973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2486 raw2973; decide +kernel
    rw [heq]
    exact (canonical2973 hH).trans (sound921 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2486 (1 : Fin 4)) =
      Sparse.eval value891 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2486 (1 : Fin 4) = raw6021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2486 raw6021; decide +kernel
    rw [heq]
    exact (canonical6021 hH).trans (sound891 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2486 (2 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2486 (2 : Fin 4) = raw6068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2486 raw6068; decide +kernel
    rw [heq]
    exact (canonical6068 hH).trans (sound907 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2486 (3 : Fin 4)) =
      Sparse.eval value911 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2486 (3 : Fin 4) = raw6082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2486 raw6082; decide +kernel
    rw [heq]
    exact (canonical6082 hH).trans (sound911 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2486 + (injectiveMoment H (mergeFirst pivotMatrix2486 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2486 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2486 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2486 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2486, value891, value907, value911, value921, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2487 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2487 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2487 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2487 = Sparse.eval value2487 (momentVector H) := by
  have heq : pivotMatrix2487 = (fun u v => node2487 (pivotPermutation2487 u) v) := by apply Matrix.ext; unfold pivotMatrix2487 node2487 pivotPermutation2487; decide +kernel
  have hmoment : injectiveMoment H node2487 = injectiveMoment H pivotMatrix2487 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2487 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2487 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2487 (0 : Fin 4)) =
      Sparse.eval value926 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2487 (0 : Fin 4) = raw6183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2487 raw6183; decide +kernel
    rw [heq]
    exact (canonical6183 hH).trans (sound926 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2487 (1 : Fin 4)) =
      Sparse.eval value891 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2487 (1 : Fin 4) = raw6025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2487 raw6025; decide +kernel
    rw [heq]
    exact (canonical6025 hH).trans (sound891 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2487 (2 : Fin 4)) =
      Sparse.eval value891 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2487 (2 : Fin 4) = raw6021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2487 raw6021; decide +kernel
    rw [heq]
    exact (canonical6021 hH).trans (sound891 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2487 (3 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2487 (3 : Fin 4) = raw6020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2487 raw6020; decide +kernel
    rw [heq]
    exact (canonical6020 hH).trans (sound464 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2487 + (injectiveMoment H (mergeFirst pivotMatrix2487 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2487 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2487 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2487 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2487, value464, value891, value926, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2488 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2488 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound2488 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2488 = Sparse.eval value2488 (momentVector H) := by
  have heq : pivotMatrix2488 = (fun u v => node2488 (pivotPermutation2488 u) v) := by apply Matrix.ext; unfold pivotMatrix2488 node2488 pivotPermutation2488; decide +kernel
  have hmoment : injectiveMoment H node2488 = injectiveMoment H pivotMatrix2488 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2488 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2488 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2488 (0 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2488 (0 : Fin 4) = raw6979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2488 raw6979; decide +kernel
    rw [heq]
    exact (canonical6979 hH).trans (sound1341 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2488 (1 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2488 (1 : Fin 4) = raw6027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2488 raw6027; decide +kernel
    rw [heq]
    exact (canonical6027 hH).trans (sound454 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2488 (2 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2488 (2 : Fin 4) = raw6022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2488 raw6022; decide +kernel
    rw [heq]
    exact (canonical6022 hH).trans (sound766 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2488 (3 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2488 (3 : Fin 4) = raw6020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2488 raw6020; decide +kernel
    rw [heq]
    exact (canonical6020 hH).trans (sound464 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2488 + (injectiveMoment H (mergeFirst pivotMatrix2488 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2488 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2488 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2488 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2488, value1341, value454, value464, value766, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2489 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2489 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem sound2489 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2489 = Sparse.eval value2489 (momentVector H) := by
  have heq : pivotMatrix2489 = (fun u v => node2489 (pivotPermutation2489 u) v) := by apply Matrix.ext; unfold pivotMatrix2489 node2489 pivotPermutation2489; decide +kernel
  have hmoment : injectiveMoment H node2489 = injectiveMoment H pivotMatrix2489 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2489 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2489 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2489 (0 : Fin 4)) =
      Sparse.eval value1334 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2489 (0 : Fin 4) = raw7055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2489 raw7055; decide +kernel
    rw [heq]
    exact (canonical7055 hH).trans (sound1334 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2489 (1 : Fin 4)) =
      Sparse.eval value1127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2489 (1 : Fin 4) = raw6028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2489 raw6028; decide +kernel
    rw [heq]
    exact (canonical6028 hH).trans (sound1127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2489 (2 : Fin 4)) =
      Sparse.eval value922 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2489 (2 : Fin 4) = raw6023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2489 raw6023; decide +kernel
    rw [heq]
    exact (canonical6023 hH).trans (sound922 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2489 (3 : Fin 4)) =
      Sparse.eval value891 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2489 (3 : Fin 4) = raw6021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2489 raw6021; decide +kernel
    rw [heq]
    exact (canonical6021 hH).trans (sound891 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2489 + (injectiveMoment H (mergeFirst pivotMatrix2489 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2489 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2489 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2489 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2489, value1127, value1334, value891, value922, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2490 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2490 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem sound2490 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2490 = Sparse.eval value2490 (momentVector H) := by
  have heq : pivotMatrix2490 = (fun u v => node2490 (pivotPermutation2490 u) v) := by apply Matrix.ext; unfold pivotMatrix2490 node2490 pivotPermutation2490; decide +kernel
  have hmoment : injectiveMoment H node2490 = injectiveMoment H pivotMatrix2490 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2490 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2490 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2490 (0 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2490 (0 : Fin 4) = raw5597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2490 raw5597; decide +kernel
    rw [heq]
    exact (canonical5597 hH).trans (sound766 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2490 (1 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2490 (1 : Fin 4) = raw6042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2490 raw6042; decide +kernel
    rw [heq]
    exact (canonical6042 hH).trans (sound894 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2490 (2 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2490 (2 : Fin 4) = raw6068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2490 raw6068; decide +kernel
    rw [heq]
    exact (canonical6068 hH).trans (sound907 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2490 (3 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2490 (3 : Fin 4) = raw6077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2490 raw6077; decide +kernel
    rw [heq]
    exact (canonical6077 hH).trans (sound910 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2490 + (injectiveMoment H (mergeFirst pivotMatrix2490 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2490 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2490 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2490 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2490, value766, value894, value907, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2491 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2491 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound2491 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2491 = Sparse.eval value2491 (momentVector H) := by
  have heq : pivotMatrix2491 = (fun u v => node2491 (pivotPermutation2491 u) v) := by apply Matrix.ext; unfold pivotMatrix2491 node2491 pivotPermutation2491; decide +kernel
  have hmoment : injectiveMoment H node2491 = injectiveMoment H pivotMatrix2491 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2491 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2491 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2491 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2491 (0 : Fin 4) = raw5600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2491 raw5600; decide +kernel
    rw [heq]
    exact (canonical5600 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2491 (1 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2491 (1 : Fin 4) = raw6043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2491 raw6043; decide +kernel
    rw [heq]
    exact (canonical6043 hH).trans (sound896 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2491 (2 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2491 (2 : Fin 4) = raw6074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2491 raw6074; decide +kernel
    rw [heq]
    exact (canonical6074 hH).trans (sound910 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2491 (3 : Fin 4)) =
      Sparse.eval value911 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2491 (3 : Fin 4) = raw6079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2491 raw6079; decide +kernel
    rw [heq]
    exact (canonical6079 hH).trans (sound911 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2491 + (injectiveMoment H (mergeFirst pivotMatrix2491 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2491 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2491 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2491 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2491, value769, value896, value910, value911, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2492 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2492 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2492 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2492 = Sparse.eval value2492 (momentVector H) := by
  have heq : pivotMatrix2492 = (fun u v => node2492 (pivotPermutation2492 u) v) := by apply Matrix.ext; unfold pivotMatrix2492 node2492 pivotPermutation2492; decide +kernel
  have hmoment : injectiveMoment H node2492 = injectiveMoment H pivotMatrix2492 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2492 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2492 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2492 (0 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2492 (0 : Fin 4) = raw5602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2492 raw5602; decide +kernel
    rw [heq]
    exact (canonical5602 hH).trans (sound1177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2492 (1 : Fin 4)) =
      Sparse.eval value897 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2492 (1 : Fin 4) = raw6045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2492 raw6045; decide +kernel
    rw [heq]
    exact (canonical6045 hH).trans (sound897 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2492 (2 : Fin 4)) =
      Sparse.eval value909 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2492 (2 : Fin 4) = raw6078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2492 raw6078; decide +kernel
    rw [heq]
    exact (canonical6078 hH).trans (sound909 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2492 (3 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2492 (3 : Fin 4) = raw6081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2492 raw6081; decide +kernel
    rw [heq]
    exact (canonical6081 hH).trans (sound1170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2492 + (injectiveMoment H (mergeFirst pivotMatrix2492 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2492 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2492 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2492 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2492, value1170, value1177, value897, value909, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2493 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2493 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem sound2493 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2493 = Sparse.eval value2493 (momentVector H) := by
  have heq : pivotMatrix2493 = (fun u v => node2493 (pivotPermutation2493 u) v) := by apply Matrix.ext; unfold pivotMatrix2493 node2493 pivotPermutation2493; decide +kernel
  have hmoment : injectiveMoment H node2493 = injectiveMoment H pivotMatrix2493 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2493 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2493 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2493 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2493 (0 : Fin 4) = raw5609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2493 raw5609; decide +kernel
    rw [heq]
    exact (canonical5609 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2493 (1 : Fin 4)) =
      Sparse.eval value898 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2493 (1 : Fin 4) = raw6047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2493 raw6047; decide +kernel
    rw [heq]
    exact (canonical6047 hH).trans (sound898 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2493 (2 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2493 (2 : Fin 4) = raw6084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2493 raw6084; decide +kernel
    rw [heq]
    exact (canonical6084 hH).trans (sound145 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2493 (3 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2493 (3 : Fin 4) = raw6087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2493 raw6087; decide +kernel
    rw [heq]
    exact (canonical6087 hH).trans (sound914 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2493 + (injectiveMoment H (mergeFirst pivotMatrix2493 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2493 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2493 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2493 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2493, value145, value771, value898, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2494 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem sound2494 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2494 = Sparse.eval value2494 (momentVector H) := by
  have heq : pivotMatrix2494 = (fun u v => node2494 (pivotPermutation2494 u) v) := by apply Matrix.ext; unfold pivotMatrix2494 node2494 pivotPermutation2494; decide +kernel
  have hmoment : injectiveMoment H node2494 = injectiveMoment H pivotMatrix2494 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2494 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2494 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2494 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2494 (0 : Fin 4) = raw5610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2494 raw5610; decide +kernel
    rw [heq]
    exact (canonical5610 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2494 (1 : Fin 4)) =
      Sparse.eval value899 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2494 (1 : Fin 4) = raw6048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2494 raw6048; decide +kernel
    rw [heq]
    exact (canonical6048 hH).trans (sound899 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2494 (2 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2494 (2 : Fin 4) = raw6086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2494 raw6086; decide +kernel
    rw [heq]
    exact (canonical6086 hH).trans (sound907 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2494 (3 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2494 (3 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2494 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2494 + (injectiveMoment H (mergeFirst pivotMatrix2494 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2494 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2494 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2494 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2494, value769, value899, value907, value915, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2495 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound2495 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2495 = Sparse.eval value2495 (momentVector H) := by
  have heq : pivotMatrix2495 = (fun u v => node2495 (pivotPermutation2495 u) v) := by apply Matrix.ext; unfold pivotMatrix2495 node2495 pivotPermutation2495; decide +kernel
  have hmoment : injectiveMoment H node2495 = injectiveMoment H pivotMatrix2495 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2495 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2495 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2495 (0 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2495 (0 : Fin 4) = raw5622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2495 raw5622; decide +kernel
    rw [heq]
    exact (canonical5622 hH).trans (sound786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2495 (1 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2495 (1 : Fin 4) = raw6052 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2495 raw6052; decide +kernel
    rw [heq]
    exact (canonical6052 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2495 (2 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2495 (2 : Fin 4) = raw6097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2495 raw6097; decide +kernel
    rw [heq]
    exact (canonical6097 hH).trans (sound914 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2495 (3 : Fin 4)) =
      Sparse.eval value921 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2495 (3 : Fin 4) = raw6101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2495 raw6101; decide +kernel
    rw [heq]
    exact (canonical6101 hH).trans (sound921 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2495 + (injectiveMoment H (mergeFirst pivotMatrix2495 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2495 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2495 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2495 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2495, value150, value786, value914, value921, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
