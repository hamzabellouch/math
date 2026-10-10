import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical100
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2496 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2496 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem sound2496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2496 = Sparse.eval value2496 (momentVector H) := by
  have heq : pivotMatrix2496 = (fun u v => node2496 (pivotPermutation2496 u) v) := by apply Matrix.ext; unfold pivotMatrix2496 node2496 pivotPermutation2496; decide +kernel
  have hmoment : injectiveMoment H node2496 = injectiveMoment H pivotMatrix2496 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2496 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2496 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2496 (0 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2496 (0 : Fin 4) = raw6220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2496 raw6220; decide +kernel
    rw [heq]
    exact (canonical6220 hH).trans (sound942 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2496 (1 : Fin 4)) =
      Sparse.eval value899 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2496 (1 : Fin 4) = raw6048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2496 raw6048; decide +kernel
    rw [heq]
    exact (canonical6048 hH).trans (sound899 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2496 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2496 (2 : Fin 4) = raw6042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2496 raw6042; decide +kernel
    rw [heq]
    exact (canonical6042 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2496 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2496 (3 : Fin 4) = raw6041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2496 raw6041; decide +kernel
    rw [heq]
    exact (canonical6041 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2496 + (injectiveMoment H (mergeFirst pivotMatrix2496 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2496 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2496 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2496 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2496, value769, value894, value899, value942, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2497 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2497 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2497 = Sparse.eval value2497 (momentVector H) := by
  have heq : pivotMatrix2497 = (fun u v => node2497 (pivotPermutation2497 u) v) := by apply Matrix.ext; unfold pivotMatrix2497 node2497 pivotPermutation2497; decide +kernel
  have hmoment : injectiveMoment H node2497 = injectiveMoment H pivotMatrix2497 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2497 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2497 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2497 (0 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2497 (0 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2497 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2497 (1 : Fin 4)) =
      Sparse.eval value902 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2497 (1 : Fin 4) = raw6049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2497 raw6049; decide +kernel
    rw [heq]
    exact (canonical6049 hH).trans (sound902 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2497 (2 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2497 (2 : Fin 4) = raw6044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2497 raw6044; decide +kernel
    rw [heq]
    exact (canonical6044 hH).trans (sound774 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2497 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2497 (3 : Fin 4) = raw6043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2497 raw6043; decide +kernel
    rw [heq]
    exact (canonical6043 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2497 + (injectiveMoment H (mergeFirst pivotMatrix2497 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2497 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2497 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2497 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2497, value774, value896, value902, value945, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2498 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2498 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2498 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2498 = Sparse.eval value2498 (momentVector H) := by
  have heq : pivotMatrix2498 = (fun u v => node2498 (pivotPermutation2498 u) v) := by apply Matrix.ext; unfold pivotMatrix2498 node2498 pivotPermutation2498; decide +kernel
  have hmoment : injectiveMoment H node2498 = injectiveMoment H pivotMatrix2498 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2498 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2498 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2498 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2498 (0 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2498 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2498 (1 : Fin 4)) =
      Sparse.eval value903 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2498 (1 : Fin 4) = raw6050 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2498 raw6050; decide +kernel
    rw [heq]
    exact (canonical6050 hH).trans (sound903 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2498 (2 : Fin 4)) =
      Sparse.eval value897 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2498 (2 : Fin 4) = raw6045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2498 raw6045; decide +kernel
    rw [heq]
    exact (canonical6045 hH).trans (sound897 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2498 (3 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2498 (3 : Fin 4) = raw6044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2498 raw6044; decide +kernel
    rw [heq]
    exact (canonical6044 hH).trans (sound774 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2498 + (injectiveMoment H (mergeFirst pivotMatrix2498 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2498 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2498 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2498 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2498, value774, value897, value903, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2499 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2499 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound2499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2499 = Sparse.eval value2499 (momentVector H) := by
  have heq : pivotMatrix2499 = (fun u v => node2499 (pivotPermutation2499 u) v) := by apply Matrix.ext; unfold pivotMatrix2499 node2499 pivotPermutation2499; decide +kernel
  have hmoment : injectiveMoment H node2499 = injectiveMoment H pivotMatrix2499 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2499 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2499 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2499 (0 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2499 (0 : Fin 4) = raw6997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2499 raw6997; decide +kernel
    rw [heq]
    exact (canonical6997 hH).trans (sound1170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2499 (1 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2499 (1 : Fin 4) = raw6074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2499 raw6074; decide +kernel
    rw [heq]
    exact (canonical6074 hH).trans (sound910 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2499 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2499 (2 : Fin 4) = raw6043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2499 raw6043; decide +kernel
    rw [heq]
    exact (canonical6043 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2499 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2499 (3 : Fin 4) = raw6041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2499 raw6041; decide +kernel
    rw [heq]
    exact (canonical6041 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2499 + (injectiveMoment H (mergeFirst pivotMatrix2499 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2499 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2499 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2499 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2499, value1170, value769, value896, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2500 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2500 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2500 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2500 = Sparse.eval value2500 (momentVector H) := by
  have heq : pivotMatrix2500 = (fun u v => node2500 (pivotPermutation2500 u) v) := by apply Matrix.ext; unfold pivotMatrix2500 node2500 pivotPermutation2500; decide +kernel
  have hmoment : injectiveMoment H node2500 = injectiveMoment H pivotMatrix2500 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2500 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2500 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2500 (0 : Fin 4)) =
      Sparse.eval value919 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2500 (0 : Fin 4) = raw7002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2500 raw7002; decide +kernel
    rw [heq]
    exact (canonical7002 hH).trans (sound919 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2500 (1 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2500 (1 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2500 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2500 (2 : Fin 4)) =
      Sparse.eval value902 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2500 (2 : Fin 4) = raw6049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2500 raw6049; decide +kernel
    rw [heq]
    exact (canonical6049 hH).trans (sound902 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2500 (3 : Fin 4)) =
      Sparse.eval value899 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2500 (3 : Fin 4) = raw6048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2500 raw6048; decide +kernel
    rw [heq]
    exact (canonical6048 hH).trans (sound899 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2500 + (injectiveMoment H (mergeFirst pivotMatrix2500 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2500 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2500 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2500 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2500, value899, value902, value915, value919, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2501 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2501 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem sound2501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2501 = Sparse.eval value2501 (momentVector H) := by
  have heq : pivotMatrix2501 = (fun u v => node2501 (pivotPermutation2501 u) v) := by apply Matrix.ext; unfold pivotMatrix2501 node2501 pivotPermutation2501; decide +kernel
  have hmoment : injectiveMoment H node2501 = injectiveMoment H pivotMatrix2501 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2501 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2501 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2501 (0 : Fin 4)) =
      Sparse.eval value966 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2501 (0 : Fin 4) = raw6261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2501 raw6261; decide +kernel
    rw [heq]
    exact (canonical6261 hH).trans (sound966 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2501 (1 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2501 (1 : Fin 4) = raw6086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2501 raw6086; decide +kernel
    rw [heq]
    exact (canonical6086 hH).trans (sound907 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2501 (2 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2501 (2 : Fin 4) = raw6068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2501 raw6068; decide +kernel
    rw [heq]
    exact (canonical6068 hH).trans (sound907 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2501 (3 : Fin 4)) =
      Sparse.eval value906 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2501 (3 : Fin 4) = raw6066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2501 raw6066; decide +kernel
    rw [heq]
    exact (canonical6066 hH).trans (sound906 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2501 + (injectiveMoment H (mergeFirst pivotMatrix2501 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2501 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2501 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2501 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2501, value906, value907, value966, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2502 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2502 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem sound2502 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2502 = Sparse.eval value2502 (momentVector H) := by
  have heq : pivotMatrix2502 = (fun u v => node2502 (pivotPermutation2502 u) v) := by apply Matrix.ext; unfold pivotMatrix2502 node2502 pivotPermutation2502; decide +kernel
  have hmoment : injectiveMoment H node2502 = injectiveMoment H pivotMatrix2502 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2502 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2502 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2502 (0 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2502 (0 : Fin 4) = raw6270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2502 raw6270; decide +kernel
    rw [heq]
    exact (canonical6270 hH).trans (sound969 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2502 (1 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2502 (1 : Fin 4) = raw6087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2502 raw6087; decide +kernel
    rw [heq]
    exact (canonical6087 hH).trans (sound914 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2502 (2 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2502 (2 : Fin 4) = raw6074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2502 raw6074; decide +kernel
    rw [heq]
    exact (canonical6074 hH).trans (sound910 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2502 (3 : Fin 4)) =
      Sparse.eval value909 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2502 (3 : Fin 4) = raw6071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2502 raw6071; decide +kernel
    rw [heq]
    exact (canonical6071 hH).trans (sound909 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2502 + (injectiveMoment H (mergeFirst pivotMatrix2502 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2502 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2502 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2502 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2502, value909, value910, value914, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2503 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2503 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2503 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2503 = Sparse.eval value2503 (momentVector H) := by
  have heq : pivotMatrix2503 = (fun u v => node2503 (pivotPermutation2503 u) v) := by apply Matrix.ext; unfold pivotMatrix2503 node2503 pivotPermutation2503; decide +kernel
  have hmoment : injectiveMoment H node2503 = injectiveMoment H pivotMatrix2503 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2503 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2503 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2503 (0 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2503 (0 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2503 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2503 (1 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2503 (1 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2503 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2503 (2 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2503 (2 : Fin 4) = raw6077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2503 raw6077; decide +kernel
    rw [heq]
    exact (canonical6077 hH).trans (sound910 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2503 (3 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2503 (3 : Fin 4) = raw6074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2503 raw6074; decide +kernel
    rw [heq]
    exact (canonical6074 hH).trans (sound910 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2503 + (injectiveMoment H (mergeFirst pivotMatrix2503 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2503 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2503 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2503 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2503, value910, value915, value970, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2504 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2504 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem sound2504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2504 = Sparse.eval value2504 (momentVector H) := by
  have heq : pivotMatrix2504 = (fun u v => node2504 (pivotPermutation2504 u) v) := by apply Matrix.ext; unfold pivotMatrix2504 node2504 pivotPermutation2504; decide +kernel
  have hmoment : injectiveMoment H node2504 = injectiveMoment H pivotMatrix2504 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2504 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2504 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2504 (0 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2504 (0 : Fin 4) = raw6280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2504 raw6280; decide +kernel
    rw [heq]
    exact (canonical6280 hH).trans (sound942 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2504 (1 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2504 (1 : Fin 4) = raw6089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2504 raw6089; decide +kernel
    rw [heq]
    exact (canonical6089 hH).trans (sound917 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2504 (2 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2504 (2 : Fin 4) = raw6080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2504 raw6080; decide +kernel
    rw [heq]
    exact (canonical6080 hH).trans (sound769 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2504 (3 : Fin 4)) =
      Sparse.eval value911 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2504 (3 : Fin 4) = raw6079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2504 raw6079; decide +kernel
    rw [heq]
    exact (canonical6079 hH).trans (sound911 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2504 + (injectiveMoment H (mergeFirst pivotMatrix2504 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2504 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2504 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2504 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2504, value769, value911, value917, value942, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2505 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2505 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2505 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2505 = Sparse.eval value2505 (momentVector H) := by
  have heq : pivotMatrix2505 = (fun u v => node2505 (pivotPermutation2505 u) v) := by apply Matrix.ext; unfold pivotMatrix2505 node2505 pivotPermutation2505; decide +kernel
  have hmoment : injectiveMoment H node2505 = injectiveMoment H pivotMatrix2505 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2505 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2505 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2505 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2505 (0 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2505 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2505 (1 : Fin 4)) =
      Sparse.eval value919 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2505 (1 : Fin 4) = raw6092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2505 raw6092; decide +kernel
    rw [heq]
    exact (canonical6092 hH).trans (sound919 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2505 (2 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2505 (2 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2505 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2505 (3 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2505 (3 : Fin 4) = raw6087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2505 raw6087; decide +kernel
    rw [heq]
    exact (canonical6087 hH).trans (sound914 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2505 + (injectiveMoment H (mergeFirst pivotMatrix2505 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2505 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2505 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2505 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2505, value914, value915, value919, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2506 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2506 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem sound2506 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2506 = Sparse.eval value2506 (momentVector H) := by
  have heq : pivotMatrix2506 = (fun u v => node2506 (pivotPermutation2506 u) v) := by apply Matrix.ext; unfold pivotMatrix2506 node2506 pivotPermutation2506; decide +kernel
  have hmoment : injectiveMoment H node2506 = injectiveMoment H pivotMatrix2506 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2506 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2506 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2506 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2506 (0 : Fin 4) = raw6290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2506 raw6290; decide +kernel
    rw [heq]
    exact (canonical6290 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2506 (1 : Fin 4)) =
      Sparse.eval value920 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2506 (1 : Fin 4) = raw6093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2506 raw6093; decide +kernel
    rw [heq]
    exact (canonical6093 hH).trans (sound920 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2506 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2506 (2 : Fin 4) = raw6090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2506 raw6090; decide +kernel
    rw [heq]
    exact (canonical6090 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2506 (3 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2506 (3 : Fin 4) = raw6089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2506 raw6089; decide +kernel
    rw [heq]
    exact (canonical6089 hH).trans (sound917 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2506 + (injectiveMoment H (mergeFirst pivotMatrix2506 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2506 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2506 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2506 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2506, value775, value917, value920, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2507 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2507 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem sound2507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2507 = Sparse.eval value2507 (momentVector H) := by
  have heq : pivotMatrix2507 = (fun u v => node2507 (pivotPermutation2507 u) v) := by apply Matrix.ext; unfold pivotMatrix2507 node2507 pivotPermutation2507; decide +kernel
  have hmoment : injectiveMoment H node2507 = injectiveMoment H pivotMatrix2507 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2507 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2507 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2507 (0 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2507 (0 : Fin 4) = raw6309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2507 raw6309; decide +kernel
    rw [heq]
    exact (canonical6309 hH).trans (sound1116 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2507 (1 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2507 (1 : Fin 4) = raw6104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2507 raw6104; decide +kernel
    rw [heq]
    exact (canonical6104 hH).trans (sound907 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2507 (2 : Fin 4)) =
      Sparse.eval value921 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2507 (2 : Fin 4) = raw6101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2507 raw6101; decide +kernel
    rw [heq]
    exact (canonical6101 hH).trans (sound921 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2507 (3 : Fin 4)) =
      Sparse.eval value1115 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2507 (3 : Fin 4) = raw6100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2507 raw6100; decide +kernel
    rw [heq]
    exact (canonical6100 hH).trans (sound1115 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2507 + (injectiveMoment H (mergeFirst pivotMatrix2507 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2507 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2507 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2507 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2507, value1115, value1116, value907, value921, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2508 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2508 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem sound2508 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2508 = Sparse.eval value2508 (momentVector H) := by
  have heq : pivotMatrix2508 = (fun u v => node2508 (pivotPermutation2508 u) v) := by apply Matrix.ext; unfold pivotMatrix2508 node2508 pivotPermutation2508; decide +kernel
  have hmoment : injectiveMoment H node2508 = injectiveMoment H pivotMatrix2508 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2508 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2508 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2508 (0 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2508 (0 : Fin 4) = raw7018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2508 raw7018; decide +kernel
    rw [heq]
    exact (canonical7018 hH).trans (sound1177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2508 (1 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2508 (1 : Fin 4) = raw6107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2508 raw6107; decide +kernel
    rw [heq]
    exact (canonical6107 hH).trans (sound766 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2508 (2 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2508 (2 : Fin 4) = raw6089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2508 raw6089; decide +kernel
    rw [heq]
    exact (canonical6089 hH).trans (sound917 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2508 (3 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2508 (3 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2508 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2508 + (injectiveMoment H (mergeFirst pivotMatrix2508 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2508 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2508 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2508 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2508, value1177, value766, value915, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2509 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2509 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound2509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2509 = Sparse.eval value2509 (momentVector H) := by
  have heq : pivotMatrix2509 = (fun u v => node2509 (pivotPermutation2509 u) v) := by apply Matrix.ext; unfold pivotMatrix2509 node2509 pivotPermutation2509; decide +kernel
  have hmoment : injectiveMoment H node2509 = injectiveMoment H pivotMatrix2509 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2509 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2509 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2509 (0 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2509 (0 : Fin 4) = raw7131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2509 raw7131; decide +kernel
    rw [heq]
    exact (canonical7131 hH).trans (sound1096 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2509 (1 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2509 (1 : Fin 4) = raw6126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2509 raw6126; decide +kernel
    rw [heq]
    exact (canonical6126 hH).trans (sound936 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2509 (2 : Fin 4)) =
      Sparse.eval value924 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2509 (2 : Fin 4) = raw6122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2509 raw6122; decide +kernel
    rw [heq]
    exact (canonical6122 hH).trans (sound924 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2509 (3 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2509 (3 : Fin 4) = raw6121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2509 raw6121; decide +kernel
    rw [heq]
    exact (canonical6121 hH).trans (sound502 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2509 + (injectiveMoment H (mergeFirst pivotMatrix2509 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2509 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2509 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2509 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2509, value1096, value502, value924, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2510 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem sound2510 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2510 = Sparse.eval value2510 (momentVector H) := by
  have heq : pivotMatrix2510 = (fun u v => node2510 (pivotPermutation2510 u) v) := by apply Matrix.ext; unfold pivotMatrix2510 node2510 pivotPermutation2510; decide +kernel
  have hmoment : injectiveMoment H node2510 = injectiveMoment H pivotMatrix2510 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2510 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2510 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2510 (0 : Fin 4)) =
      Sparse.eval value1299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2510 (0 : Fin 4) = raw1768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2510 raw1768; decide +kernel
    rw [heq]
    exact (canonical1768 hH).trans (sound1299 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2510 (1 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2510 (1 : Fin 4) = raw6125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2510 raw6125; decide +kernel
    rw [heq]
    exact (canonical6125 hH).trans (sound477 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2510 (2 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2510 (2 : Fin 4) = raw6211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2510 raw6211; decide +kernel
    rw [heq]
    exact (canonical6211 hH).trans (sound969 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2510 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2510 (3 : Fin 4) = raw6213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2510 raw6213; decide +kernel
    rw [heq]
    exact (canonical6213 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2510 + (injectiveMoment H (mergeFirst pivotMatrix2510 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2510 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2510 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2510 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2510, value1299, value477, value936, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2511 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem sound2511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2511 = Sparse.eval value2511 (momentVector H) := by
  have heq : pivotMatrix2511 = (fun u v => node2511 (pivotPermutation2511 u) v) := by apply Matrix.ext; unfold pivotMatrix2511 node2511 pivotPermutation2511; decide +kernel
  have hmoment : injectiveMoment H node2511 = injectiveMoment H pivotMatrix2511 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2511 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2511 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2511 (0 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2511 (0 : Fin 4) = raw2044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2511 raw2044; decide +kernel
    rw [heq]
    exact (canonical2044 hH).trans (sound1099 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2511 (1 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2511 (1 : Fin 4) = raw6176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2511 raw6176; decide +kernel
    rw [heq]
    exact (canonical6176 hH).trans (sound936 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2511 (2 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2511 (2 : Fin 4) = raw6305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2511 raw6305; decide +kernel
    rw [heq]
    exact (canonical6305 hH).trans (sound939 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2511 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2511 (3 : Fin 4) = raw6313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2511 raw6313; decide +kernel
    rw [heq]
    exact (canonical6313 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2511 + (injectiveMoment H (mergeFirst pivotMatrix2511 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2511 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2511 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2511 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2511, value1099, value936, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2512 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2512 = Sparse.eval value2512 (momentVector H) := by
  have heq : pivotMatrix2512 = (fun u v => node2512 (pivotPermutation2512 u) v) := by apply Matrix.ext; unfold pivotMatrix2512 node2512 pivotPermutation2512; decide +kernel
  have hmoment : injectiveMoment H node2512 = injectiveMoment H pivotMatrix2512 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2512 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2512 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2512 (0 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2512 (0 : Fin 4) = raw2069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2512 raw2069; decide +kernel
    rw [heq]
    exact (canonical2069 hH).trans (sound936 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2512 (1 : Fin 4)) =
      Sparse.eval value926 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2512 (1 : Fin 4) = raw6183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2512 raw6183; decide +kernel
    rw [heq]
    exact (canonical6183 hH).trans (sound926 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2512 (2 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2512 (2 : Fin 4) = raw6316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2512 raw6316; decide +kernel
    rw [heq]
    exact (canonical6316 hH).trans (sound942 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2512 (3 : Fin 4)) =
      Sparse.eval value966 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2512 (3 : Fin 4) = raw6322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2512 raw6322; decide +kernel
    rw [heq]
    exact (canonical6322 hH).trans (sound966 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2512 + (injectiveMoment H (mergeFirst pivotMatrix2512 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2512 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2512 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2512 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2512, value926, value936, value942, value966, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2513 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2513 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2513 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2513 = Sparse.eval value2513 (momentVector H) := by
  have heq : pivotMatrix2513 = (fun u v => node2513 (pivotPermutation2513 u) v) := by apply Matrix.ext; unfold pivotMatrix2513 node2513 pivotPermutation2513; decide +kernel
  have hmoment : injectiveMoment H node2513 = injectiveMoment H pivotMatrix2513 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2513 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2513 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2513 (0 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2513 (0 : Fin 4) = raw7047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2513 raw7047; decide +kernel
    rw [heq]
    exact (canonical7047 hH).trans (sound1123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2513 (1 : Fin 4)) =
      Sparse.eval value926 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2513 (1 : Fin 4) = raw6183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2513 raw6183; decide +kernel
    rw [heq]
    exact (canonical6183 hH).trans (sound926 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2513 (2 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2513 (2 : Fin 4) = raw6142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2513 raw6142; decide +kernel
    rw [heq]
    exact (canonical6142 hH).trans (sound942 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2513 (3 : Fin 4)) =
      Sparse.eval value515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2513 (3 : Fin 4) = raw6141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2513 raw6141; decide +kernel
    rw [heq]
    exact (canonical6141 hH).trans (sound515 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2513 + (injectiveMoment H (mergeFirst pivotMatrix2513 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2513 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2513 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2513 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2513, value1123, value515, value926, value942, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2514 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2514 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound2514 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2514 = Sparse.eval value2514 (momentVector H) := by
  have heq : pivotMatrix2514 = (fun u v => node2514 (pivotPermutation2514 u) v) := by apply Matrix.ext; unfold pivotMatrix2514 node2514 pivotPermutation2514; decide +kernel
  have hmoment : injectiveMoment H node2514 = injectiveMoment H pivotMatrix2514 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2514 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2514 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2514 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2514 (0 : Fin 4) = raw7134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2514 raw7134; decide +kernel
    rw [heq]
    exact (canonical7134 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2514 (1 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2514 (1 : Fin 4) = raw6191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2514 raw6191; decide +kernel
    rw [heq]
    exact (canonical6191 hH).trans (sound680 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2514 (2 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2514 (2 : Fin 4) = raw6143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2514 raw6143; decide +kernel
    rw [heq]
    exact (canonical6143 hH).trans (sound943 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2514 (3 : Fin 4)) =
      Sparse.eval value515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2514 (3 : Fin 4) = raw6141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2514 raw6141; decide +kernel
    rw [heq]
    exact (canonical6141 hH).trans (sound515 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2514 + (injectiveMoment H (mergeFirst pivotMatrix2514 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2514 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2514 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2514 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2514, value1078, value515, value680, value943, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2515 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2515 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem sound2515 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2515 = Sparse.eval value2515 (momentVector H) := by
  have heq : pivotMatrix2515 = (fun u v => node2515 (pivotPermutation2515 u) v) := by apply Matrix.ext; unfold pivotMatrix2515 node2515 pivotPermutation2515; decide +kernel
  have hmoment : injectiveMoment H node2515 = injectiveMoment H pivotMatrix2515 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2515 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2515 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2515 (0 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2515 (0 : Fin 4) = raw8029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2515 raw8029; decide +kernel
    rw [heq]
    exact (canonical8029 hH).trans (sound1007 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2515 (1 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2515 (1 : Fin 4) = raw6221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2515 raw6221; decide +kernel
    rw [heq]
    exact (canonical6221 hH).trans (sound943 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2515 (2 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2515 (2 : Fin 4) = raw6143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2515 raw6143; decide +kernel
    rw [heq]
    exact (canonical6143 hH).trans (sound943 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2515 (3 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2515 (3 : Fin 4) = raw6136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2515 raw6136; decide +kernel
    rw [heq]
    exact (canonical6136 hH).trans (sound944 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2515 + (injectiveMoment H (mergeFirst pivotMatrix2515 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2515 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2515 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2515 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2515, value1007, value943, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2516 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2516 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem sound2516 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2516 = Sparse.eval value2516 (momentVector H) := by
  have heq : pivotMatrix2516 = (fun u v => node2516 (pivotPermutation2516 u) v) := by apply Matrix.ext; unfold pivotMatrix2516 node2516 pivotPermutation2516; decide +kernel
  have hmoment : injectiveMoment H node2516 = injectiveMoment H pivotMatrix2516 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2516 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2516 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2516 (0 : Fin 4)) =
      Sparse.eval value1011 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (0 : Fin 4) = raw8030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw8030; decide +kernel
    rw [heq]
    exact (canonical8030 hH).trans (sound1011 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2516 (1 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (1 : Fin 4) = raw6226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw6226; decide +kernel
    rw [heq]
    exact (canonical6226 hH).trans (sound948 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2516 (2 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (2 : Fin 4) = raw6158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw6158; decide +kernel
    rw [heq]
    exact (canonical6158 hH).trans (sound948 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2516 (3 : Fin 4)) =
      Sparse.eval value953 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (3 : Fin 4) = raw6146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw6146; decide +kernel
    rw [heq]
    exact (canonical6146 hH).trans (sound953 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2516 + (injectiveMoment H (mergeFirst pivotMatrix2516 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2516 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2516 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2516 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2516, value1011, value948, value953, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2517 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2517 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2517 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2517 = Sparse.eval value2517 (momentVector H) := by
  have heq : pivotMatrix2517 = (fun u v => node2517 (pivotPermutation2517 u) v) := by apply Matrix.ext; unfold pivotMatrix2517 node2517 pivotPermutation2517; decide +kernel
  have hmoment : injectiveMoment H node2517 = injectiveMoment H pivotMatrix2517 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2517 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2517 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2517 (0 : Fin 4)) =
      Sparse.eval value1124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (0 : Fin 4) = raw7051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw7051; decide +kernel
    rw [heq]
    exact (canonical7051 hH).trans (sound1124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2517 (1 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (1 : Fin 4) = raw6190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw6190; decide +kernel
    rw [heq]
    exact (canonical6190 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2517 (2 : Fin 4)) =
      Sparse.eval value949 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (2 : Fin 4) = raw6159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw6159; decide +kernel
    rw [heq]
    exact (canonical6159 hH).trans (sound949 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2517 (3 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (3 : Fin 4) = raw6157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw6157; decide +kernel
    rw [heq]
    exact (canonical6157 hH).trans (sound1018 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2517 + (injectiveMoment H (mergeFirst pivotMatrix2517 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2517 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2517 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2517 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2517, value1018, value1123, value1124, value949, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2518 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2518 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem sound2518 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2518 = Sparse.eval value2518 (momentVector H) := by
  have heq : pivotMatrix2518 = (fun u v => node2518 (pivotPermutation2518 u) v) := by apply Matrix.ext; unfold pivotMatrix2518 node2518 pivotPermutation2518; decide +kernel
  have hmoment : injectiveMoment H node2518 = injectiveMoment H pivotMatrix2518 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2518 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2518 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2518 (0 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2518 (0 : Fin 4) = raw7136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2518 raw7136; decide +kernel
    rw [heq]
    exact (canonical7136 hH).trans (sound1123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2518 (1 : Fin 4)) =
      Sparse.eval value925 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2518 (1 : Fin 4) = raw6193 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2518 raw6193; decide +kernel
    rw [heq]
    exact (canonical6193 hH).trans (sound925 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2518 (2 : Fin 4)) =
      Sparse.eval value949 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2518 (2 : Fin 4) = raw6159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2518 raw6159; decide +kernel
    rw [heq]
    exact (canonical6159 hH).trans (sound949 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2518 (3 : Fin 4)) =
      Sparse.eval value509 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2518 (3 : Fin 4) = raw6156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2518 raw6156; decide +kernel
    rw [heq]
    exact (canonical6156 hH).trans (sound509 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2518 + (injectiveMoment H (mergeFirst pivotMatrix2518 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2518 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2518 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2518 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2518, value1123, value509, value925, value949, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2519 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2519 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound2519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2519 = Sparse.eval value2519 (momentVector H) := by
  have heq : pivotMatrix2519 = (fun u v => node2519 (pivotPermutation2519 u) v) := by apply Matrix.ext; unfold pivotMatrix2519 node2519 pivotPermutation2519; decide +kernel
  have hmoment : injectiveMoment H node2519 = injectiveMoment H pivotMatrix2519 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2519 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2519 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2519 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2519 (0 : Fin 4) = raw7137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2519 raw7137; decide +kernel
    rw [heq]
    exact (canonical7137 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2519 (1 : Fin 4)) =
      Sparse.eval value1105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2519 (1 : Fin 4) = raw6194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2519 raw6194; decide +kernel
    rw [heq]
    exact (canonical6194 hH).trans (sound1105 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2519 (2 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2519 (2 : Fin 4) = raw6160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2519 raw6160; decide +kernel
    rw [heq]
    exact (canonical6160 hH).trans (sound950 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2519 (3 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2519 (3 : Fin 4) = raw6157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2519 raw6157; decide +kernel
    rw [heq]
    exact (canonical6157 hH).trans (sound1018 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2519 + (injectiveMoment H (mergeFirst pivotMatrix2519 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2519 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2519 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2519 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2519, value1018, value1079, value1105, value950, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2520 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2520 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2520 = Sparse.eval value2520 (momentVector H) := by
  have heq : pivotMatrix2520 = (fun u v => node2520 (pivotPermutation2520 u) v) := by apply Matrix.ext; unfold pivotMatrix2520 node2520 pivotPermutation2520; decide +kernel
  have hmoment : injectiveMoment H node2520 = injectiveMoment H pivotMatrix2520 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2520 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2520 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2520 (0 : Fin 4)) =
      Sparse.eval value1354 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2520 (0 : Fin 4) = raw7052 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2520 raw7052; decide +kernel
    rw [heq]
    exact (canonical7052 hH).trans (sound1354 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2520 (1 : Fin 4)) =
      Sparse.eval value1157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2520 (1 : Fin 4) = raw6195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2520 raw6195; decide +kernel
    rw [heq]
    exact (canonical6195 hH).trans (sound1157 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2520 (2 : Fin 4)) =
      Sparse.eval value986 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2520 (2 : Fin 4) = raw6171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2520 raw6171; decide +kernel
    rw [heq]
    exact (canonical6171 hH).trans (sound986 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2520 (3 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2520 (3 : Fin 4) = raw6169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2520 raw6169; decide +kernel
    rw [heq]
    exact (canonical6169 hH).trans (sound1341 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2520 + (injectiveMoment H (mergeFirst pivotMatrix2520 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2520 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2520 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2520 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2520, value1157, value1341, value1354, value986, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2521 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2521 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem sound2521 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2521 = Sparse.eval value2521 (momentVector H) := by
  have heq : pivotMatrix2521 = (fun u v => node2521 (pivotPermutation2521 u) v) := by apply Matrix.ext; unfold pivotMatrix2521 node2521 pivotPermutation2521; decide +kernel
  have hmoment : injectiveMoment H node2521 = injectiveMoment H pivotMatrix2521 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2521 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2521 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2521 (0 : Fin 4)) =
      Sparse.eval value1363 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2521 (0 : Fin 4) = raw7053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2521 raw7053; decide +kernel
    rw [heq]
    exact (canonical7053 hH).trans (sound1363 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2521 (1 : Fin 4)) =
      Sparse.eval value1358 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2521 (1 : Fin 4) = raw6196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2521 raw6196; decide +kernel
    rw [heq]
    exact (canonical6196 hH).trans (sound1358 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2521 (2 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2521 (2 : Fin 4) = raw6172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2521 raw6172; decide +kernel
    rw [heq]
    exact (canonical6172 hH).trans (sound972 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2521 (3 : Fin 4)) =
      Sparse.eval value925 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2521 (3 : Fin 4) = raw6170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2521 raw6170; decide +kernel
    rw [heq]
    exact (canonical6170 hH).trans (sound925 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2521 + (injectiveMoment H (mergeFirst pivotMatrix2521 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2521 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2521 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2521 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2521, value1358, value1363, value925, value972, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2522 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2522 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound2522 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2522 = Sparse.eval value2522 (momentVector H) := by
  have heq : pivotMatrix2522 = (fun u v => node2522 (pivotPermutation2522 u) v) := by apply Matrix.ext; unfold pivotMatrix2522 node2522 pivotPermutation2522; decide +kernel
  have hmoment : injectiveMoment H node2522 = injectiveMoment H pivotMatrix2522 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2522 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2522 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2522 (0 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2522 (0 : Fin 4) = raw7142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2522 raw7142; decide +kernel
    rw [heq]
    exact (canonical7142 hH).trans (sound972 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2522 (1 : Fin 4)) =
      Sparse.eval value980 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2522 (1 : Fin 4) = raw6197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2522 raw6197; decide +kernel
    rw [heq]
    exact (canonical6197 hH).trans (sound980 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2522 (2 : Fin 4)) =
      Sparse.eval value986 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2522 (2 : Fin 4) = raw6173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2522 raw6173; decide +kernel
    rw [heq]
    exact (canonical6173 hH).trans (sound986 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2522 (3 : Fin 4)) =
      Sparse.eval value925 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2522 (3 : Fin 4) = raw6170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2522 raw6170; decide +kernel
    rw [heq]
    exact (canonical6170 hH).trans (sound925 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2522 + (injectiveMoment H (mergeFirst pivotMatrix2522 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2522 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2522 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2522 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2522, value925, value972, value980, value986, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2523 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2523 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem sound2523 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2523 = Sparse.eval value2523 (momentVector H) := by
  have heq : pivotMatrix2523 = (fun u v => node2523 (pivotPermutation2523 u) v) := by apply Matrix.ext; unfold pivotMatrix2523 node2523 pivotPermutation2523; decide +kernel
  have hmoment : injectiveMoment H node2523 = injectiveMoment H pivotMatrix2523 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2523 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2523 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2523 (0 : Fin 4)) =
      Sparse.eval value1332 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2523 (0 : Fin 4) = raw8292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2523 raw8292; decide +kernel
    rw [heq]
    exact (canonical8292 hH).trans (sound1332 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2523 (1 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2523 (1 : Fin 4) = raw6301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2523 raw6301; decide +kernel
    rw [heq]
    exact (canonical6301 hH).trans (sound983 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2523 (2 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2523 (2 : Fin 4) = raw6174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2523 raw6174; decide +kernel
    rw [heq]
    exact (canonical6174 hH).trans (sound502 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2523 (3 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2523 (3 : Fin 4) = raw6166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2523 raw6166; decide +kernel
    rw [heq]
    exact (canonical6166 hH).trans (sound502 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2523 + (injectiveMoment H (mergeFirst pivotMatrix2523 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2523 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2523 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2523 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2523, value1332, value502, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2524 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2524 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2524 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2524 = Sparse.eval value2524 (momentVector H) := by
  have heq : pivotMatrix2524 = (fun u v => node2524 (pivotPermutation2524 u) v) := by apply Matrix.ext; unfold pivotMatrix2524 node2524 pivotPermutation2524; decide +kernel
  have hmoment : injectiveMoment H node2524 = injectiveMoment H pivotMatrix2524 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2524 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2524 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2524 (0 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2524 (0 : Fin 4) = raw8032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2524 raw8032; decide +kernel
    rw [heq]
    exact (canonical8032 hH).trans (sound985 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2524 (1 : Fin 4)) =
      Sparse.eval value962 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2524 (1 : Fin 4) = raw6242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2524 raw6242; decide +kernel
    rw [heq]
    exact (canonical6242 hH).trans (sound962 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2524 (2 : Fin 4)) =
      Sparse.eval value986 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2524 (2 : Fin 4) = raw6173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2524 raw6173; decide +kernel
    rw [heq]
    exact (canonical6173 hH).trans (sound986 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2524 (3 : Fin 4)) =
      Sparse.eval value712 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2524 (3 : Fin 4) = raw6168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2524 raw6168; decide +kernel
    rw [heq]
    exact (canonical6168 hH).trans (sound712 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2524 + (injectiveMoment H (mergeFirst pivotMatrix2524 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2524 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2524 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2524 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2524, value712, value962, value985, value986, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2525 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound2525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2525 = Sparse.eval value2525 (momentVector H) := by
  have heq : pivotMatrix2525 = (fun u v => node2525 (pivotPermutation2525 u) v) := by apply Matrix.ext; unfold pivotMatrix2525 node2525 pivotPermutation2525; decide +kernel
  have hmoment : injectiveMoment H node2525 = injectiveMoment H pivotMatrix2525 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2525 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2525 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2525 (0 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2525 (0 : Fin 4) = raw3221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2525 raw3221; decide +kernel
    rw [heq]
    exact (canonical3221 hH).trans (sound977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2525 (1 : Fin 4)) =
      Sparse.eval value980 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2525 (1 : Fin 4) = raw6197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2525 raw6197; decide +kernel
    rw [heq]
    exact (canonical6197 hH).trans (sound980 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2525 (2 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2525 (2 : Fin 4) = raw6307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2525 raw6307; decide +kernel
    rw [heq]
    exact (canonical6307 hH).trans (sound978 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2525 (3 : Fin 4)) =
      Sparse.eval value960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2525 (3 : Fin 4) = raw6314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2525 raw6314; decide +kernel
    rw [heq]
    exact (canonical6314 hH).trans (sound960 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2525 + (injectiveMoment H (mergeFirst pivotMatrix2525 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2525 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2525 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2525 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2525, value960, value977, value978, value980, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2526 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

theorem sound2526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2526 = Sparse.eval value2526 (momentVector H) := by
  have heq : pivotMatrix2526 = (fun u v => node2526 (pivotPermutation2526 u) v) := by apply Matrix.ext; unfold pivotMatrix2526 node2526 pivotPermutation2526; decide +kernel
  have hmoment : injectiveMoment H node2526 = injectiveMoment H pivotMatrix2526 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2526 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2526 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2526 (0 : Fin 4)) =
      Sparse.eval value1282 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (0 : Fin 4) = raw3236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw3236; decide +kernel
    rw [heq]
    exact (canonical3236 hH).trans (sound1282 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2526 (1 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (1 : Fin 4) = raw6199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw6199; decide +kernel
    rw [heq]
    exact (canonical6199 hH).trans (sound604 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2526 (2 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (2 : Fin 4) = raw6318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw6318; decide +kernel
    rw [heq]
    exact (canonical6318 hH).trans (sound977 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2526 (3 : Fin 4)) =
      Sparse.eval value982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (3 : Fin 4) = raw6323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw6323; decide +kernel
    rw [heq]
    exact (canonical6323 hH).trans (sound982 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2526 + (injectiveMoment H (mergeFirst pivotMatrix2526 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2526 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2526 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2526 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2526, value1282, value604, value977, value982, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2527 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2527 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem sound2527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2527 = Sparse.eval value2527 (momentVector H) := by
  have heq : pivotMatrix2527 = (fun u v => node2527 (pivotPermutation2527 u) v) := by apply Matrix.ext; unfold pivotMatrix2527 node2527 pivotPermutation2527; decide +kernel
  have hmoment : injectiveMoment H node2527 = injectiveMoment H pivotMatrix2527 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2527 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2527 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2527 (0 : Fin 4)) =
      Sparse.eval value1334 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2527 (0 : Fin 4) = raw7055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2527 raw7055; decide +kernel
    rw [heq]
    exact (canonical7055 hH).trans (sound1334 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2527 (1 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2527 (1 : Fin 4) = raw6198 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2527 raw6198; decide +kernel
    rw [heq]
    exact (canonical6198 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2527 (2 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2527 (2 : Fin 4) = raw6185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2527 raw6185; decide +kernel
    rw [heq]
    exact (canonical6185 hH).trans (sound936 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2527 (3 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2527 (3 : Fin 4) = raw6184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2527 raw6184; decide +kernel
    rw [heq]
    exact (canonical6184 hH).trans (sound680 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2527 + (injectiveMoment H (mergeFirst pivotMatrix2527 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2527 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2527 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2527 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2527, value1249, value1334, value680, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2528 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2528 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem sound2528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2528 = Sparse.eval value2528 (momentVector H) := by
  have heq : pivotMatrix2528 = (fun u v => node2528 (pivotPermutation2528 u) v) := by apply Matrix.ext; unfold pivotMatrix2528 node2528 pivotPermutation2528; decide +kernel
  have hmoment : injectiveMoment H node2528 = injectiveMoment H pivotMatrix2528 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2528 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2528 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2528 (0 : Fin 4)) =
      Sparse.eval value1333 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2528 (0 : Fin 4) = raw7144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2528 raw7144; decide +kernel
    rw [heq]
    exact (canonical7144 hH).trans (sound1333 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2528 (1 : Fin 4)) =
      Sparse.eval value679 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2528 (1 : Fin 4) = raw6200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2528 raw6200; decide +kernel
    rw [heq]
    exact (canonical6200 hH).trans (sound679 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2528 (2 : Fin 4)) =
      Sparse.eval value984 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2528 (2 : Fin 4) = raw6186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2528 raw6186; decide +kernel
    rw [heq]
    exact (canonical6186 hH).trans (sound984 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2528 (3 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2528 (3 : Fin 4) = raw6184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2528 raw6184; decide +kernel
    rw [heq]
    exact (canonical6184 hH).trans (sound680 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2528 + (injectiveMoment H (mergeFirst pivotMatrix2528 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2528 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2528 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2528 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2528, value1333, value679, value680, value984, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2529 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2529 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2529 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2529 = Sparse.eval value2529 (momentVector H) := by
  have heq : pivotMatrix2529 = (fun u v => node2529 (pivotPermutation2529 u) v) := by apply Matrix.ext; unfold pivotMatrix2529 node2529 pivotPermutation2529; decide +kernel
  have hmoment : injectiveMoment H node2529 = injectiveMoment H pivotMatrix2529 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2529 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2529 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2529 (0 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2529 (0 : Fin 4) = raw5627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2529 raw5627; decide +kernel
    rw [heq]
    exact (canonical5627 hH).trans (sound1170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2529 (1 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2529 (1 : Fin 4) = raw6246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2529 raw6246; decide +kernel
    rw [heq]
    exact (canonical6246 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2529 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2529 (2 : Fin 4) = raw6317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2529 raw6317; decide +kernel
    rw [heq]
    exact (canonical6317 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2529 (3 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2529 (3 : Fin 4) = raw6321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2529 raw6321; decide +kernel
    rw [heq]
    exact (canonical6321 hH).trans (sound972 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2529 + (injectiveMoment H (mergeFirst pivotMatrix2529 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2529 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2529 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2529 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2529, value1170, value285, value972, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2530 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2530 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem sound2530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2530 = Sparse.eval value2530 (momentVector H) := by
  have heq : pivotMatrix2530 = (fun u v => node2530 (pivotPermutation2530 u) v) := by apply Matrix.ext; unfold pivotMatrix2530 node2530 pivotPermutation2530; decide +kernel
  have hmoment : injectiveMoment H node2530 = injectiveMoment H pivotMatrix2530 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2530 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2530 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2530 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2530 (0 : Fin 4) = raw5677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2530 raw5677; decide +kernel
    rw [heq]
    exact (canonical5677 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2530 (1 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2530 (1 : Fin 4) = raw6218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2530 raw6218; decide +kernel
    rw [heq]
    exact (canonical6218 hH).trans (sound939 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2530 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2530 (2 : Fin 4) = raw6255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2530 raw6255; decide +kernel
    rw [heq]
    exact (canonical6255 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2530 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2530 (3 : Fin 4) = raw6270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2530 raw6270; decide +kernel
    rw [heq]
    exact (canonical6270 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2530 + (injectiveMoment H (mergeFirst pivotMatrix2530 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2530 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2530 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2530 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2530, value1202, value271, value939, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2531 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2531 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem sound2531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2531 = Sparse.eval value2531 (momentVector H) := by
  have heq : pivotMatrix2531 = (fun u v => node2531 (pivotPermutation2531 u) v) := by apply Matrix.ext; unfold pivotMatrix2531 node2531 pivotPermutation2531; decide +kernel
  have hmoment : injectiveMoment H node2531 = injectiveMoment H pivotMatrix2531 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2531 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2531 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2531 (0 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (0 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2531 (1 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (1 : Fin 4) = raw6220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw6220; decide +kernel
    rw [heq]
    exact (canonical6220 hH).trans (sound942 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2531 (2 : Fin 4)) =
      Sparse.eval value966 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (2 : Fin 4) = raw6261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw6261; decide +kernel
    rw [heq]
    exact (canonical6261 hH).trans (sound966 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2531 (3 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (3 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2531 + (injectiveMoment H (mergeFirst pivotMatrix2531 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2531 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2531 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2531 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2531, value942, value966, value969, value970, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2532 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2532 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2532 = Sparse.eval value2532 (momentVector H) := by
  have heq : pivotMatrix2532 = (fun u v => node2532 (pivotPermutation2532 u) v) := by apply Matrix.ext; unfold pivotMatrix2532 node2532 pivotPermutation2532; decide +kernel
  have hmoment : injectiveMoment H node2532 = injectiveMoment H pivotMatrix2532 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2532 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2532 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2532 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (0 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2532 (1 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (1 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2532 (2 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (2 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2532 (3 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (3 : Fin 4) = raw6280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw6280; decide +kernel
    rw [heq]
    exact (canonical6280 hH).trans (sound942 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2532 + (injectiveMoment H (mergeFirst pivotMatrix2532 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2532 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2532 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2532 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2532, value942, value945, value970, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2533 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2533 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2533 = Sparse.eval value2533 (momentVector H) := by
  have heq : pivotMatrix2533 = (fun u v => node2533 (pivotPermutation2533 u) v) := by apply Matrix.ext; unfold pivotMatrix2533 node2533 pivotPermutation2533; decide +kernel
  have hmoment : injectiveMoment H node2533 = injectiveMoment H pivotMatrix2533 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2533 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2533 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2533 (0 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2533 (0 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2533 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2533 (1 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2533 (1 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2533 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2533 (2 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2533 (2 : Fin 4) = raw6278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2533 raw6278; decide +kernel
    rw [heq]
    exact (canonical6278 hH).trans (sound969 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2533 (3 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2533 (3 : Fin 4) = raw6281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2533 raw6281; decide +kernel
    rw [heq]
    exact (canonical6281 hH).trans (sound974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2533 + (injectiveMoment H (mergeFirst pivotMatrix2533 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2533 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2533 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2533 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2533, value1221, value946, value969, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2534 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2534 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2534 = Sparse.eval value2534 (momentVector H) := by
  have heq : pivotMatrix2534 = (fun u v => node2534 (pivotPermutation2534 u) v) := by apply Matrix.ext; unfold pivotMatrix2534 node2534 pivotPermutation2534; decide +kernel
  have hmoment : injectiveMoment H node2534 = injectiveMoment H pivotMatrix2534 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2534 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2534 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2534 (0 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2534 (0 : Fin 4) = raw5709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2534 raw5709; decide +kernel
    rw [heq]
    exact (canonical5709 hH).trans (sound1203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2534 (1 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2534 (1 : Fin 4) = raw6245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2534 raw6245; decide +kernel
    rw [heq]
    exact (canonical6245 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2534 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2534 (2 : Fin 4) = raw6306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2534 raw6306; decide +kernel
    rw [heq]
    exact (canonical6306 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2534 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2534 (3 : Fin 4) = raw6310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2534 raw6310; decide +kernel
    rw [heq]
    exact (canonical6310 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2534 + (injectiveMoment H (mergeFirst pivotMatrix2534 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2534 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2534 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2534 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2534, value1203, value271, value936, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2535 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2535 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2535 = Sparse.eval value2535 (momentVector H) := by
  have heq : pivotMatrix2535 = (fun u v => node2535 (pivotPermutation2535 u) v) := by apply Matrix.ext; unfold pivotMatrix2535 node2535 pivotPermutation2535; decide +kernel
  have hmoment : injectiveMoment H node2535 = injectiveMoment H pivotMatrix2535 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2535 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2535 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2535 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2535 (0 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2535 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2535 (1 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2535 (1 : Fin 4) = raw6246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2535 raw6246; decide +kernel
    rw [heq]
    exact (canonical6246 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2535 (2 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2535 (2 : Fin 4) = raw6307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2535 raw6307; decide +kernel
    rw [heq]
    exact (canonical6307 hH).trans (sound978 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2535 (3 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2535 (3 : Fin 4) = raw6311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2535 raw6311; decide +kernel
    rw [heq]
    exact (canonical6311 hH).trans (sound1268 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2535 + (injectiveMoment H (mergeFirst pivotMatrix2535 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2535 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2535 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2535 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2535, value1063, value1268, value285, value978, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2536 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2536 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2536 = Sparse.eval value2536 (momentVector H) := by
  have heq : pivotMatrix2536 = (fun u v => node2536 (pivotPermutation2536 u) v) := by apply Matrix.ext; unfold pivotMatrix2536 node2536 pivotPermutation2536; decide +kernel
  have hmoment : injectiveMoment H node2536 = injectiveMoment H pivotMatrix2536 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2536 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2536 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2536 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2536 (0 : Fin 4) = raw5714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2536 raw5714; decide +kernel
    rw [heq]
    exact (canonical5714 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2536 (1 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2536 (1 : Fin 4) = raw6278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2536 raw6278; decide +kernel
    rw [heq]
    exact (canonical6278 hH).trans (sound969 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2536 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2536 (2 : Fin 4) = raw6317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2536 raw6317; decide +kernel
    rw [heq]
    exact (canonical6317 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2536 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2536 (3 : Fin 4) = raw6320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2536 raw6320; decide +kernel
    rw [heq]
    exact (canonical6320 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2536 + (injectiveMoment H (mergeFirst pivotMatrix2536 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2536 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2536 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2536 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2536, value1202, value969, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2537 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2537 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem sound2537 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2537 = Sparse.eval value2537 (momentVector H) := by
  have heq : pivotMatrix2537 = (fun u v => node2537 (pivotPermutation2537 u) v) := by apply Matrix.ext; unfold pivotMatrix2537 node2537 pivotPermutation2537; decide +kernel
  have hmoment : injectiveMoment H node2537 = injectiveMoment H pivotMatrix2537 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2537 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2537 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2537 (0 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2537 (0 : Fin 4) = raw6412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2537 raw6412; decide +kernel
    rw [heq]
    exact (canonical6412 hH).trans (sound1000 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2537 (1 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2537 (1 : Fin 4) = raw6228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2537 raw6228; decide +kernel
    rw [heq]
    exact (canonical6228 hH).trans (sound950 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2537 (2 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2537 (2 : Fin 4) = raw6221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2537 raw6221; decide +kernel
    rw [heq]
    exact (canonical6221 hH).trans (sound943 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2537 (3 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2537 (3 : Fin 4) = raw6220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2537 raw6220; decide +kernel
    rw [heq]
    exact (canonical6220 hH).trans (sound942 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2537 + (injectiveMoment H (mergeFirst pivotMatrix2537 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2537 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2537 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2537 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2537, value1000, value942, value943, value950, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2538 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2538 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound2538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2538 = Sparse.eval value2538 (momentVector H) := by
  have heq : pivotMatrix2538 = (fun u v => node2538 (pivotPermutation2538 u) v) := by apply Matrix.ext; unfold pivotMatrix2538 node2538 pivotPermutation2538; decide +kernel
  have hmoment : injectiveMoment H node2538 = injectiveMoment H pivotMatrix2538 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2538 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2538 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2538 (0 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2538 (0 : Fin 4) = raw6414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2538 raw6414; decide +kernel
    rw [heq]
    exact (canonical6414 hH).trans (sound1008 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2538 (1 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2538 (1 : Fin 4) = raw6229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2538 raw6229; decide +kernel
    rw [heq]
    exact (canonical6229 hH).trans (sound951 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2538 (2 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2538 (2 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2538 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2538 (3 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2538 (3 : Fin 4) = raw6222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2538 raw6222; decide +kernel
    rw [heq]
    exact (canonical6222 hH).trans (sound944 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2538 + (injectiveMoment H (mergeFirst pivotMatrix2538 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2538 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2538 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2538 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2538, value1008, value944, value945, value951, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2539 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2539 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound2539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2539 = Sparse.eval value2539 (momentVector H) := by
  have heq : pivotMatrix2539 = (fun u v => node2539 (pivotPermutation2539 u) v) := by apply Matrix.ext; unfold pivotMatrix2539 node2539 pivotPermutation2539; decide +kernel
  have hmoment : injectiveMoment H node2539 = injectiveMoment H pivotMatrix2539 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2539 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2539 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2539 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2539 (0 : Fin 4) = raw6415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2539 raw6415; decide +kernel
    rw [heq]
    exact (canonical6415 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2539 (1 : Fin 4)) =
      Sparse.eval value952 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2539 (1 : Fin 4) = raw6230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2539 raw6230; decide +kernel
    rw [heq]
    exact (canonical6230 hH).trans (sound952 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2539 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2539 (2 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2539 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2539 (3 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2539 (3 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2539 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2539 + (injectiveMoment H (mergeFirst pivotMatrix2539 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2539 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2539 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2539 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2539, value1009, value945, value946, value952, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2540 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2540 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem sound2540 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2540 = Sparse.eval value2540 (momentVector H) := by
  have heq : pivotMatrix2540 = (fun u v => node2540 (pivotPermutation2540 u) v) := by apply Matrix.ext; unfold pivotMatrix2540 node2540 pivotPermutation2540; decide +kernel
  have hmoment : injectiveMoment H node2540 = injectiveMoment H pivotMatrix2540 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2540 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2540 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2540 (0 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2540 (0 : Fin 4) = raw7080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2540 raw7080; decide +kernel
    rw [heq]
    exact (canonical7080 hH).trans (sound1206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2540 (1 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2540 (1 : Fin 4) = raw6270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2540 raw6270; decide +kernel
    rw [heq]
    exact (canonical6270 hH).trans (sound969 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2540 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2540 (2 : Fin 4) = raw6222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2540 raw6222; decide +kernel
    rw [heq]
    exact (canonical6222 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2540 (3 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2540 (3 : Fin 4) = raw6218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2540 raw6218; decide +kernel
    rw [heq]
    exact (canonical6218 hH).trans (sound939 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2540 + (injectiveMoment H (mergeFirst pivotMatrix2540 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2540 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2540 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2540 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2540, value1206, value939, value944, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2541 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2541 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2541 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2541 = Sparse.eval value2541 (momentVector H) := by
  have heq : pivotMatrix2541 = (fun u v => node2541 (pivotPermutation2541 u) v) := by apply Matrix.ext; unfold pivotMatrix2541 node2541 pivotPermutation2541; decide +kernel
  have hmoment : injectiveMoment H node2541 = injectiveMoment H pivotMatrix2541 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2541 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2541 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2541 (0 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2541 (0 : Fin 4) = raw7082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2541 raw7082; decide +kernel
    rw [heq]
    exact (canonical7082 hH).trans (sound1207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2541 (1 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2541 (1 : Fin 4) = raw6278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2541 raw6278; decide +kernel
    rw [heq]
    exact (canonical6278 hH).trans (sound969 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2541 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2541 (2 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2541 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2541 (3 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2541 (3 : Fin 4) = raw6221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2541 raw6221; decide +kernel
    rw [heq]
    exact (canonical6221 hH).trans (sound943 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2541 + (injectiveMoment H (mergeFirst pivotMatrix2541 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2541 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2541 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2541 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2541, value1207, value943, value946, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2542 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2542 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2542 = Sparse.eval value2542 (momentVector H) := by
  have heq : pivotMatrix2542 = (fun u v => node2542 (pivotPermutation2542 u) v) := by apply Matrix.ext; unfold pivotMatrix2542 node2542 pivotPermutation2542; decide +kernel
  have hmoment : injectiveMoment H node2542 = injectiveMoment H pivotMatrix2542 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2542 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2542 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2542 (0 : Fin 4)) =
      Sparse.eval value1246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2542 (0 : Fin 4) = raw7178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2542 raw7178; decide +kernel
    rw [heq]
    exact (canonical7178 hH).trans (sound1246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2542 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2542 (1 : Fin 4) = raw6288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2542 raw6288; decide +kernel
    rw [heq]
    exact (canonical6288 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2542 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2542 (2 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2542 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2542 (3 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2542 (3 : Fin 4) = raw6220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2542 raw6220; decide +kernel
    rw [heq]
    exact (canonical6220 hH).trans (sound942 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2542 + (injectiveMoment H (mergeFirst pivotMatrix2542 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2542 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2542 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2542 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2542, value1246, value942, value946, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2543 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2543 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2543 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2543 = Sparse.eval value2543 (momentVector H) := by
  have heq : pivotMatrix2543 = (fun u v => node2543 (pivotPermutation2543 u) v) := by apply Matrix.ext; unfold pivotMatrix2543 node2543 pivotPermutation2543; decide +kernel
  have hmoment : injectiveMoment H node2543 = injectiveMoment H pivotMatrix2543 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2543 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2543 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2543 (0 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2543 (0 : Fin 4) = raw7182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2543 raw7182; decide +kernel
    rw [heq]
    exact (canonical7182 hH).trans (sound1206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2543 (1 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2543 (1 : Fin 4) = raw6293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2543 raw6293; decide +kernel
    rw [heq]
    exact (canonical6293 hH).trans (sound977 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2543 (2 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2543 (2 : Fin 4) = raw6229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2543 raw6229; decide +kernel
    rw [heq]
    exact (canonical6229 hH).trans (sound951 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2543 (3 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2543 (3 : Fin 4) = raw6226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2543 raw6226; decide +kernel
    rw [heq]
    exact (canonical6226 hH).trans (sound948 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2543 + (injectiveMoment H (mergeFirst pivotMatrix2543 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2543 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2543 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2543 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2543, value1206, value948, value951, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2544 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2544 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2544 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2544 = Sparse.eval value2544 (momentVector H) := by
  have heq : pivotMatrix2544 = (fun u v => node2544 (pivotPermutation2544 u) v) := by apply Matrix.ext; unfold pivotMatrix2544 node2544 pivotPermutation2544; decide +kernel
  have hmoment : injectiveMoment H node2544 = injectiveMoment H pivotMatrix2544 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2544 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2544 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2544 (0 : Fin 4)) =
      Sparse.eval value1211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2544 (0 : Fin 4) = raw7086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2544 raw7086; decide +kernel
    rw [heq]
    exact (canonical7086 hH).trans (sound1211 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2544 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2544 (1 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2544 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2544 (2 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2544 (2 : Fin 4) = raw6229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2544 raw6229; decide +kernel
    rw [heq]
    exact (canonical6229 hH).trans (sound951 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2544 (3 : Fin 4)) =
      Sparse.eval value949 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2544 (3 : Fin 4) = raw6227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2544 raw6227; decide +kernel
    rw [heq]
    exact (canonical6227 hH).trans (sound949 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2544 + (injectiveMoment H (mergeFirst pivotMatrix2544 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2544 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2544 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2544 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2544, value1211, value949, value951, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2545 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2545 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2545 = Sparse.eval value2545 (momentVector H) := by
  have heq : pivotMatrix2545 = (fun u v => node2545 (pivotPermutation2545 u) v) := by apply Matrix.ext; unfold pivotMatrix2545 node2545 pivotPermutation2545; decide +kernel
  have hmoment : injectiveMoment H node2545 = injectiveMoment H pivotMatrix2545 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2545 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2545 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2545 (0 : Fin 4)) =
      Sparse.eval value1212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (0 : Fin 4) = raw7087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw7087; decide +kernel
    rw [heq]
    exact (canonical7087 hH).trans (sound1212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2545 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (1 : Fin 4) = raw6288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw6288; decide +kernel
    rw [heq]
    exact (canonical6288 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2545 (2 : Fin 4)) =
      Sparse.eval value952 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (2 : Fin 4) = raw6230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw6230; decide +kernel
    rw [heq]
    exact (canonical6230 hH).trans (sound952 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2545 (3 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (3 : Fin 4) = raw6228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw6228; decide +kernel
    rw [heq]
    exact (canonical6228 hH).trans (sound950 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2545 + (injectiveMoment H (mergeFirst pivotMatrix2545 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2545 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2545 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2545 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2545, value1212, value950, value952, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2546 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2546 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem sound2546 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2546 = Sparse.eval value2546 (momentVector H) := by
  have heq : pivotMatrix2546 = (fun u v => node2546 (pivotPermutation2546 u) v) := by apply Matrix.ext; unfold pivotMatrix2546 node2546 pivotPermutation2546; decide +kernel
  have hmoment : injectiveMoment H node2546 = injectiveMoment H pivotMatrix2546 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2546 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2546 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2546 (0 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2546 (0 : Fin 4) = raw7183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2546 raw7183; decide +kernel
    rw [heq]
    exact (canonical7183 hH).trans (sound1207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2546 (1 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2546 (1 : Fin 4) = raw6296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2546 raw6296; decide +kernel
    rw [heq]
    exact (canonical6296 hH).trans (sound977 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2546 (2 : Fin 4)) =
      Sparse.eval value953 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2546 (2 : Fin 4) = raw6231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2546 raw6231; decide +kernel
    rw [heq]
    exact (canonical6231 hH).trans (sound953 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2546 (3 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2546 (3 : Fin 4) = raw6228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2546 raw6228; decide +kernel
    rw [heq]
    exact (canonical6228 hH).trans (sound950 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2546 + (injectiveMoment H (mergeFirst pivotMatrix2546 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2546 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2546 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2546 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2546, value1207, value950, value953, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2547 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2547 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2547 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2547 = Sparse.eval value2547 (momentVector H) := by
  have heq : pivotMatrix2547 = (fun u v => node2547 (pivotPermutation2547 u) v) := by apply Matrix.ext; unfold pivotMatrix2547 node2547 pivotPermutation2547; decide +kernel
  have hmoment : injectiveMoment H node2547 = injectiveMoment H pivotMatrix2547 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2547 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2547 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2547 (0 : Fin 4)) =
      Sparse.eval value919 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2547 (0 : Fin 4) = raw6092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2547 raw6092; decide +kernel
    rw [heq]
    exact (canonical6092 hH).trans (sound919 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2547 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2547 (1 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2547 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2547 (2 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2547 (2 : Fin 4) = raw6293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2547 raw6293; decide +kernel
    rw [heq]
    exact (canonical6293 hH).trans (sound977 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2547 (3 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2547 (3 : Fin 4) = raw6295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2547 raw6295; decide +kernel
    rw [heq]
    exact (canonical6295 hH).trans (sound978 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2547 + (injectiveMoment H (mergeFirst pivotMatrix2547 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2547 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2547 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2547 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2547, value919, value974, value977, value978, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2548 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2548 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem sound2548 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2548 = Sparse.eval value2548 (momentVector H) := by
  have heq : pivotMatrix2548 = (fun u v => node2548 (pivotPermutation2548 u) v) := by apply Matrix.ext; unfold pivotMatrix2548 node2548 pivotPermutation2548; decide +kernel
  have hmoment : injectiveMoment H node2548 = injectiveMoment H pivotMatrix2548 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2548 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2548 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2548 (0 : Fin 4)) =
      Sparse.eval value1115 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2548 (0 : Fin 4) = raw6100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2548 raw6100; decide +kernel
    rw [heq]
    exact (canonical6100 hH).trans (sound1115 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2548 (1 : Fin 4)) =
      Sparse.eval value982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2548 (1 : Fin 4) = raw6300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2548 raw6300; decide +kernel
    rw [heq]
    exact (canonical6300 hH).trans (sound982 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2548 (2 : Fin 4)) =
      Sparse.eval value960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2548 (2 : Fin 4) = raw6308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2548 raw6308; decide +kernel
    rw [heq]
    exact (canonical6308 hH).trans (sound960 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2548 (3 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2548 (3 : Fin 4) = raw6309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2548 raw6309; decide +kernel
    rw [heq]
    exact (canonical6309 hH).trans (sound1116 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2548 + (injectiveMoment H (mergeFirst pivotMatrix2548 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2548 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2548 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2548 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2548, value1115, value1116, value960, value982, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2549 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2549 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2549 = Sparse.eval value2549 (momentVector H) := by
  have heq : pivotMatrix2549 = (fun u v => node2549 (pivotPermutation2549 u) v) := by apply Matrix.ext; unfold pivotMatrix2549 node2549 pivotPermutation2549; decide +kernel
  have hmoment : injectiveMoment H node2549 = injectiveMoment H pivotMatrix2549 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2549 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2549 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2549 (0 : Fin 4)) =
      Sparse.eval value1228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2549 (0 : Fin 4) = raw6102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2549 raw6102; decide +kernel
    rw [heq]
    exact (canonical6102 hH).trans (sound1228 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2549 (1 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2549 (1 : Fin 4) = raw6303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2549 raw6303; decide +kernel
    rw [heq]
    exact (canonical6303 hH).trans (sound985 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2549 (2 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2549 (2 : Fin 4) = raw6311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2549 raw6311; decide +kernel
    rw [heq]
    exact (canonical6311 hH).trans (sound1268 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2549 (3 : Fin 4)) =
      Sparse.eval value986 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2549 (3 : Fin 4) = raw6312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2549 raw6312; decide +kernel
    rw [heq]
    exact (canonical6312 hH).trans (sound986 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2549 + (injectiveMoment H (mergeFirst pivotMatrix2549 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2549 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2549 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2549 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2549, value1228, value1268, value985, value986, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2550 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2550 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

theorem sound2550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2550 = Sparse.eval value2550 (momentVector H) := by
  have heq : pivotMatrix2550 = (fun u v => node2550 (pivotPermutation2550 u) v) := by apply Matrix.ext; unfold pivotMatrix2550 node2550 pivotPermutation2550; decide +kernel
  have hmoment : injectiveMoment H node2550 = injectiveMoment H pivotMatrix2550 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2550 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2550 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2550 (0 : Fin 4)) =
      Sparse.eval value1045 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2550 (0 : Fin 4) = raw6481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2550 raw6481; decide +kernel
    rw [heq]
    exact (canonical6481 hH).trans (sound1045 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2550 (1 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2550 (1 : Fin 4) = raw6285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2550 raw6285; decide +kernel
    rw [heq]
    exact (canonical6285 hH).trans (sound967 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2550 (2 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2550 (2 : Fin 4) = raw6263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2550 raw6263; decide +kernel
    rw [heq]
    exact (canonical6263 hH).trans (sound967 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2550 (3 : Fin 4)) =
      Sparse.eval value966 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2550 (3 : Fin 4) = raw6261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2550 raw6261; decide +kernel
    rw [heq]
    exact (canonical6261 hH).trans (sound966 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2550 + (injectiveMoment H (mergeFirst pivotMatrix2550 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2550 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2550 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2550 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2550, value1045, value966, value967, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2551 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2551 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2551 = Sparse.eval value2551 (momentVector H) := by
  have heq : pivotMatrix2551 = (fun u v => node2551 (pivotPermutation2551 u) v) := by apply Matrix.ext; unfold pivotMatrix2551 node2551 pivotPermutation2551; decide +kernel
  have hmoment : injectiveMoment H node2551 = injectiveMoment H pivotMatrix2551 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2551 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2551 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2551 (0 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (0 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2551 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (1 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2551 (2 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (2 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2551 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (3 : Fin 4) = raw6270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6270; decide +kernel
    rw [heq]
    exact (canonical6270 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2551 + (injectiveMoment H (mergeFirst pivotMatrix2551 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2551 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2551 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2551 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2551, value1048, value969, value970, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2552 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2552 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem sound2552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2552 = Sparse.eval value2552 (momentVector H) := by
  have heq : pivotMatrix2552 = (fun u v => node2552 (pivotPermutation2552 u) v) := by apply Matrix.ext; unfold pivotMatrix2552 node2552 pivotPermutation2552; decide +kernel
  have hmoment : injectiveMoment H node2552 = injectiveMoment H pivotMatrix2552 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2552 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2552 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2552 (0 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2552 (0 : Fin 4) = raw6490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2552 raw6490; decide +kernel
    rw [heq]
    exact (canonical6490 hH).trans (sound1000 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2552 (1 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2552 (1 : Fin 4) = raw6289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2552 raw6289; decide +kernel
    rw [heq]
    exact (canonical6289 hH).trans (sound975 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2552 (2 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2552 (2 : Fin 4) = raw6280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2552 raw6280; decide +kernel
    rw [heq]
    exact (canonical6280 hH).trans (sound942 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2552 (3 : Fin 4)) =
      Sparse.eval value971 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2552 (3 : Fin 4) = raw6279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2552 raw6279; decide +kernel
    rw [heq]
    exact (canonical6279 hH).trans (sound971 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2552 + (injectiveMoment H (mergeFirst pivotMatrix2552 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2552 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2552 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2552 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2552, value1000, value942, value971, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2553 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2553 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem sound2553 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2553 = Sparse.eval value2553 (momentVector H) := by
  have heq : pivotMatrix2553 = (fun u v => node2553 (pivotPermutation2553 u) v) := by apply Matrix.ext; unfold pivotMatrix2553 node2553 pivotPermutation2553; decide +kernel
  have hmoment : injectiveMoment H node2553 = injectiveMoment H pivotMatrix2553 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2553 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2553 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2553 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2553 (0 : Fin 4) = raw6492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2553 raw6492; decide +kernel
    rw [heq]
    exact (canonical6492 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2553 (1 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2553 (1 : Fin 4) = raw6291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2553 raw6291; decide +kernel
    rw [heq]
    exact (canonical6291 hH).trans (sound976 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2553 (2 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2553 (2 : Fin 4) = raw6282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2553 raw6282; decide +kernel
    rw [heq]
    exact (canonical6282 hH).trans (sound972 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2553 (3 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2553 (3 : Fin 4) = raw6281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2553 raw6281; decide +kernel
    rw [heq]
    exact (canonical6281 hH).trans (sound974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2553 + (injectiveMoment H (mergeFirst pivotMatrix2553 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2553 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2553 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2553 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2553, value1265, value972, value974, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2554 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2554 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2554 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2554 = Sparse.eval value2554 (momentVector H) := by
  have heq : pivotMatrix2554 = (fun u v => node2554 (pivotPermutation2554 u) v) := by apply Matrix.ext; unfold pivotMatrix2554 node2554 pivotPermutation2554; decide +kernel
  have hmoment : injectiveMoment H node2554 = injectiveMoment H pivotMatrix2554 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2554 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2554 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2554 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2554 (0 : Fin 4) = raw6498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2554 raw6498; decide +kernel
    rw [heq]
    exact (canonical6498 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2554 (1 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2554 (1 : Fin 4) = raw6293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2554 raw6293; decide +kernel
    rw [heq]
    exact (canonical6293 hH).trans (sound977 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2554 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2554 (2 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2554 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2554 (3 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2554 (3 : Fin 4) = raw6286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2554 raw6286; decide +kernel
    rw [heq]
    exact (canonical6286 hH).trans (sound973 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2554 + (injectiveMoment H (mergeFirst pivotMatrix2554 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2554 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2554 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2554 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2554, value1053, value973, value974, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2555 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2555 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem sound2555 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2555 = Sparse.eval value2555 (momentVector H) := by
  have heq : pivotMatrix2555 = (fun u v => node2555 (pivotPermutation2555 u) v) := by apply Matrix.ext; unfold pivotMatrix2555 node2555 pivotPermutation2555; decide +kernel
  have hmoment : injectiveMoment H node2555 = injectiveMoment H pivotMatrix2555 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2555 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2555 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2555 (0 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2555 (0 : Fin 4) = raw6503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2555 raw6503; decide +kernel
    rw [heq]
    exact (canonical6503 hH).trans (sound1054 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2555 (1 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2555 (1 : Fin 4) = raw6295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2555 raw6295; decide +kernel
    rw [heq]
    exact (canonical6295 hH).trans (sound978 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2555 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2555 (2 : Fin 4) = raw6288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2555 raw6288; decide +kernel
    rw [heq]
    exact (canonical6288 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2555 (3 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2555 (3 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2555 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2555 + (injectiveMoment H (mergeFirst pivotMatrix2555 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2555 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2555 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2555 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2555, value1054, value974, value978, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2556 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem sound2556 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2556 = Sparse.eval value2556 (momentVector H) := by
  have heq : pivotMatrix2556 = (fun u v => node2556 (pivotPermutation2556 u) v) := by apply Matrix.ext; unfold pivotMatrix2556 node2556 pivotPermutation2556; decide +kernel
  have hmoment : injectiveMoment H node2556 = injectiveMoment H pivotMatrix2556 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2556 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2556 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2556 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2556 (0 : Fin 4) = raw6507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2556 raw6507; decide +kernel
    rw [heq]
    exact (canonical6507 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2556 (1 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2556 (1 : Fin 4) = raw6297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2556 raw6297; decide +kernel
    rw [heq]
    exact (canonical6297 hH).trans (sound979 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2556 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2556 (2 : Fin 4) = raw6290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2556 raw6290; decide +kernel
    rw [heq]
    exact (canonical6290 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2556 (3 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2556 (3 : Fin 4) = raw6289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2556 raw6289; decide +kernel
    rw [heq]
    exact (canonical6289 hH).trans (sound975 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2556 + (injectiveMoment H (mergeFirst pivotMatrix2556 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2556 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2556 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2556 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2556, value1057, value946, value975, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2557 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem sound2557 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2557 = Sparse.eval value2557 (momentVector H) := by
  have heq : pivotMatrix2557 = (fun u v => node2557 (pivotPermutation2557 u) v) := by apply Matrix.ext; unfold pivotMatrix2557 node2557 pivotPermutation2557; decide +kernel
  have hmoment : injectiveMoment H node2557 = injectiveMoment H pivotMatrix2557 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2557 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2557 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2557 (0 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2557 (0 : Fin 4) = raw6528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2557 raw6528; decide +kernel
    rw [heq]
    exact (canonical6528 hH).trans (sound837 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2557 (1 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2557 (1 : Fin 4) = raw6309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2557 raw6309; decide +kernel
    rw [heq]
    exact (canonical6309 hH).trans (sound1116 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2557 (2 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2557 (2 : Fin 4) = raw6301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2557 raw6301; decide +kernel
    rw [heq]
    exact (canonical6301 hH).trans (sound983 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2557 (3 : Fin 4)) =
      Sparse.eval value982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2557 (3 : Fin 4) = raw6300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2557 raw6300; decide +kernel
    rw [heq]
    exact (canonical6300 hH).trans (sound982 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2557 + (injectiveMoment H (mergeFirst pivotMatrix2557 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2557 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2557 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2557 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2557, value1116, value837, value982, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2558 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

theorem sound2558 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2558 = Sparse.eval value2558 (momentVector H) := by
  have heq : pivotMatrix2558 = (fun u v => node2558 (pivotPermutation2558 u) v) := by apply Matrix.ext; unfold pivotMatrix2558 node2558 pivotPermutation2558; decide +kernel
  have hmoment : injectiveMoment H node2558 = injectiveMoment H pivotMatrix2558 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2558 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2558 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2558 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2558 (0 : Fin 4) = raw6535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2558 raw6535; decide +kernel
    rw [heq]
    exact (canonical6535 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2558 (1 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2558 (1 : Fin 4) = raw6319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2558 raw6319; decide +kernel
    rw [heq]
    exact (canonical6319 hH).trans (sound1116 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2558 (2 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2558 (2 : Fin 4) = raw6309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2558 raw6309; decide +kernel
    rw [heq]
    exact (canonical6309 hH).trans (sound1116 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2558 (3 : Fin 4)) =
      Sparse.eval value960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2558 (3 : Fin 4) = raw6308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2558 raw6308; decide +kernel
    rw [heq]
    exact (canonical6308 hH).trans (sound960 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2558 + (injectiveMoment H (mergeFirst pivotMatrix2558 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2558 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2558 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2558 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2558, value1040, value1116, value960, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2559 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2559 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem sound2559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2559 = Sparse.eval value2559 (momentVector H) := by
  have heq : pivotMatrix2559 = (fun u v => node2559 (pivotPermutation2559 u) v) := by apply Matrix.ext; unfold pivotMatrix2559 node2559 pivotPermutation2559; decide +kernel
  have hmoment : injectiveMoment H node2559 = injectiveMoment H pivotMatrix2559 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2559 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2559 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2559 (0 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2559 (0 : Fin 4) = raw6542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2559 raw6542; decide +kernel
    rw [heq]
    exact (canonical6542 hH).trans (sound1260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2559 (1 : Fin 4)) =
      Sparse.eval value987 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2559 (1 : Fin 4) = raw6325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2559 raw6325; decide +kernel
    rw [heq]
    exact (canonical6325 hH).trans (sound987 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2559 (2 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2559 (2 : Fin 4) = raw6321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2559 raw6321; decide +kernel
    rw [heq]
    exact (canonical6321 hH).trans (sound972 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2559 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2559 (3 : Fin 4) = raw6320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2559 raw6320; decide +kernel
    rw [heq]
    exact (canonical6320 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2559 + (injectiveMoment H (mergeFirst pivotMatrix2559 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2559 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2559 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2559 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2559, value1260, value969, value972, value987, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
