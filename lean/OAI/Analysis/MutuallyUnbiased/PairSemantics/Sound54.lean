import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical264
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical265
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical283
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical289

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation3456 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3456 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem sound3456 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3456 = Sparse.eval value3456 (momentVector H) := by
  have heq : pivotMatrix3456 = (fun u v => node3456 (pivotPermutation3456 u) v) := by apply Matrix.ext; unfold pivotMatrix3456 node3456 pivotPermutation3456; decide +kernel
  have hmoment : injectiveMoment H node3456 = injectiveMoment H pivotMatrix3456 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3456 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3456 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3456 (0 : Fin 5)) =
      Sparse.eval value2403 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3456 (0 : Fin 5) = raw6064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3456 raw6064; decide +kernel
    rw [heq]
    exact (canonical6064 hH).trans (sound2403 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3456 (1 : Fin 5)) =
      Sparse.eval value2825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3456 (1 : Fin 5) = raw8272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3456 raw8272; decide +kernel
    rw [heq]
    exact (canonical8272 hH).trans (sound2825 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3456 (2 : Fin 5)) =
      Sparse.eval value2825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3456 (2 : Fin 5) = raw8280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3456 raw8280; decide +kernel
    rw [heq]
    exact (canonical8280 hH).trans (sound2825 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3456 (3 : Fin 5)) =
      Sparse.eval value2853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3456 (3 : Fin 5) = raw8282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3456 raw8282; decide +kernel
    rw [heq]
    exact (canonical8282 hH).trans (sound2853 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3456 (4 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3456 (4 : Fin 5) = raw8283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3456 raw8283; decide +kernel
    rw [heq]
    exact (canonical8283 hH).trans (sound653 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3456 + (injectiveMoment H (mergeFirst pivotMatrix3456 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3456 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3456 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3456 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3456 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3456, value2403, value2825, value2853, value653, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3457 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3457 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem sound3457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3457 = Sparse.eval value3457 (momentVector H) := by
  have heq : pivotMatrix3457 = (fun u v => node3457 (pivotPermutation3457 u) v) := by apply Matrix.ext; unfold pivotMatrix3457 node3457 pivotPermutation3457; decide +kernel
  have hmoment : injectiveMoment H node3457 = injectiveMoment H pivotMatrix3457 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3457 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3457 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3457 (0 : Fin 5)) =
      Sparse.eval value2551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3457 (0 : Fin 5) = raw6274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3457 raw6274; decide +kernel
    rw [heq]
    exact (canonical6274 hH).trans (sound2551 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3457 (1 : Fin 5)) =
      Sparse.eval value2819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3457 (1 : Fin 5) = raw8290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3457 raw8290; decide +kernel
    rw [heq]
    exact (canonical8290 hH).trans (sound2819 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3457 (2 : Fin 5)) =
      Sparse.eval value2813 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3457 (2 : Fin 5) = raw8297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3457 raw8297; decide +kernel
    rw [heq]
    exact (canonical8297 hH).trans (sound2813 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3457 (3 : Fin 5)) =
      Sparse.eval value2813 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3457 (3 : Fin 5) = raw8299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3457 raw8299; decide +kernel
    rw [heq]
    exact (canonical8299 hH).trans (sound2813 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3457 (4 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3457 (4 : Fin 5) = raw8300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3457 raw8300; decide +kernel
    rw [heq]
    exact (canonical8300 hH).trans (sound570 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3457 + (injectiveMoment H (mergeFirst pivotMatrix3457 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3457 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3457 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3457 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3457 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3457, value2551, value2813, value2819, value570, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3458 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3458 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem sound3458 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3458 = Sparse.eval value3458 (momentVector H) := by
  have heq : pivotMatrix3458 = (fun u v => node3458 (pivotPermutation3458 u) v) := by apply Matrix.ext; unfold pivotMatrix3458 node3458 pivotPermutation3458; decide +kernel
  have hmoment : injectiveMoment H node3458 = injectiveMoment H pivotMatrix3458 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3458 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3458 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3458 (0 : Fin 5)) =
      Sparse.eval value2647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3458 (0 : Fin 5) = raw6674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3458 raw6674; decide +kernel
    rw [heq]
    exact (canonical6674 hH).trans (sound2647 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3458 (1 : Fin 5)) =
      Sparse.eval value2830 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3458 (1 : Fin 5) = raw8365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3458 raw8365; decide +kernel
    rw [heq]
    exact (canonical8365 hH).trans (sound2830 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3458 (2 : Fin 5)) =
      Sparse.eval value2857 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3458 (2 : Fin 5) = raw8472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3458 raw8472; decide +kernel
    rw [heq]
    exact (canonical8472 hH).trans (sound2857 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3458 (3 : Fin 5)) =
      Sparse.eval value2857 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3458 (3 : Fin 5) = raw8479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3458 raw8479; decide +kernel
    rw [heq]
    exact (canonical8479 hH).trans (sound2857 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3458 (4 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3458 (4 : Fin 5) = raw8480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3458 raw8480; decide +kernel
    rw [heq]
    exact (canonical8480 hH).trans (sound1151 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3458 + (injectiveMoment H (mergeFirst pivotMatrix3458 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3458 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3458 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3458 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3458 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3458, value1151, value2647, value2830, value2857, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3459 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3459 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem sound3459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3459 = Sparse.eval value3459 (momentVector H) := by
  have heq : pivotMatrix3459 = (fun u v => node3459 (pivotPermutation3459 u) v) := by apply Matrix.ext; unfold pivotMatrix3459 node3459 pivotPermutation3459; decide +kernel
  have hmoment : injectiveMoment H node3459 = injectiveMoment H pivotMatrix3459 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3459 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3459 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3459 (0 : Fin 5)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3459 (0 : Fin 5) = raw7337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3459 raw7337; decide +kernel
    rw [heq]
    exact (canonical7337 hH).trans (sound2749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3459 (1 : Fin 5)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3459 (1 : Fin 5) = raw9186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3459 raw9186; decide +kernel
    rw [heq]
    exact (canonical9186 hH).trans (sound2749 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3459 (2 : Fin 5)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3459 (2 : Fin 5) = raw9243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3459 raw9243; decide +kernel
    rw [heq]
    exact (canonical9243 hH).trans (sound2749 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3459 (3 : Fin 5)) =
      Sparse.eval value2862 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3459 (3 : Fin 5) = raw9262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3459 raw9262; decide +kernel
    rw [heq]
    exact (canonical9262 hH).trans (sound2862 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3459 (4 : Fin 5)) =
      Sparse.eval value437 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3459 (4 : Fin 5) = raw9267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3459 raw9267; decide +kernel
    rw [heq]
    exact (canonical9267 hH).trans (sound437 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3459 + (injectiveMoment H (mergeFirst pivotMatrix3459 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3459 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3459 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3459 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3459 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3459, value2749, value2862, value437, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3460 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3460 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem sound3460 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3460 = Sparse.eval value3460 (momentVector H) := by
  have heq : pivotMatrix3460 = (fun u v => node3460 (pivotPermutation3460 u) v) := by apply Matrix.ext; unfold pivotMatrix3460 node3460 pivotPermutation3460; decide +kernel
  have hmoment : injectiveMoment H node3460 = injectiveMoment H pivotMatrix3460 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3460 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3460 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3460 (0 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3460 (0 : Fin 5) = raw7502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3460 raw7502; decide +kernel
    rw [heq]
    exact (canonical7502 hH).trans (sound2823 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3460 (1 : Fin 5)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3460 (1 : Fin 5) = raw7573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3460 raw7573; decide +kernel
    rw [heq]
    exact (canonical7573 hH).trans (sound959 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3460 (2 : Fin 5)) =
      Sparse.eval value2731 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3460 (2 : Fin 5) = raw7575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3460 raw7575; decide +kernel
    rw [heq]
    exact (canonical7575 hH).trans (sound2731 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3460 (3 : Fin 5)) =
      Sparse.eval value2731 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3460 (3 : Fin 5) = raw7576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3460 raw7576; decide +kernel
    rw [heq]
    exact (canonical7576 hH).trans (sound2731 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3460 (4 : Fin 5)) =
      Sparse.eval value2832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3460 (4 : Fin 5) = raw7577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3460 raw7577; decide +kernel
    rw [heq]
    exact (canonical7577 hH).trans (sound2832 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3460 + (injectiveMoment H (mergeFirst pivotMatrix3460 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3460 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3460 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3460 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3460 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3460, value2731, value2823, value2832, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3461 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3461 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound3461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3461 = Sparse.eval value3461 (momentVector H) := by
  have heq : pivotMatrix3461 = (fun u v => node3461 (pivotPermutation3461 u) v) := by apply Matrix.ext; unfold pivotMatrix3461 node3461 pivotPermutation3461; decide +kernel
  have hmoment : injectiveMoment H node3461 = injectiveMoment H pivotMatrix3461 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3461 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3461 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3461 (0 : Fin 5)) =
      Sparse.eval value1823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3461 (0 : Fin 5) = raw7804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3461 raw7804; decide +kernel
    rw [heq]
    exact (canonical7804 hH).trans (sound1823 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3461 (1 : Fin 5)) =
      Sparse.eval value2835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3461 (1 : Fin 5) = raw7770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3461 raw7770; decide +kernel
    rw [heq]
    exact (canonical7770 hH).trans (sound2835 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3461 (2 : Fin 5)) =
      Sparse.eval value2834 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3461 (2 : Fin 5) = raw7765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3461 raw7765; decide +kernel
    rw [heq]
    exact (canonical7765 hH).trans (sound2834 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3461 (3 : Fin 5)) =
      Sparse.eval value2833 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3461 (3 : Fin 5) = raw7764 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3461 raw7764; decide +kernel
    rw [heq]
    exact (canonical7764 hH).trans (sound2833 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3461 (4 : Fin 5)) =
      Sparse.eval value2833 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3461 (4 : Fin 5) = raw7763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3461 raw7763; decide +kernel
    rw [heq]
    exact (canonical7763 hH).trans (sound2833 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3461 + (injectiveMoment H (mergeFirst pivotMatrix3461 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3461 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3461 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3461 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3461 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3461, value1823, value2833, value2834, value2835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3462 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound3462 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3462 = Sparse.eval value3462 (momentVector H) := by
  have heq : pivotMatrix3462 = (fun u v => node3462 (pivotPermutation3462 u) v) := by apply Matrix.ext; unfold pivotMatrix3462 node3462 pivotPermutation3462; decide +kernel
  have hmoment : injectiveMoment H node3462 = injectiveMoment H pivotMatrix3462 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3462 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3462 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3462 (0 : Fin 5)) =
      Sparse.eval value2618 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3462 (0 : Fin 5) = raw7831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3462 raw7831; decide +kernel
    rw [heq]
    exact (canonical7831 hH).trans (sound2618 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3462 (1 : Fin 5)) =
      Sparse.eval value1748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3462 (1 : Fin 5) = raw7800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3462 raw7800; decide +kernel
    rw [heq]
    exact (canonical7800 hH).trans (sound1748 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3462 (2 : Fin 5)) =
      Sparse.eval value2839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3462 (2 : Fin 5) = raw7791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3462 raw7791; decide +kernel
    rw [heq]
    exact (canonical7791 hH).trans (sound2839 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3462 (3 : Fin 5)) =
      Sparse.eval value2838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3462 (3 : Fin 5) = raw7790 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3462 raw7790; decide +kernel
    rw [heq]
    exact (canonical7790 hH).trans (sound2838 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3462 (4 : Fin 5)) =
      Sparse.eval value2837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3462 (4 : Fin 5) = raw7789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3462 raw7789; decide +kernel
    rw [heq]
    exact (canonical7789 hH).trans (sound2837 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3462 + (injectiveMoment H (mergeFirst pivotMatrix3462 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3462 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3462 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3462 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3462 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3462, value1748, value2618, value2837, value2838, value2839, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3463 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound3463 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3463 = Sparse.eval value3463 (momentVector H) := by
  have heq : pivotMatrix3463 = (fun u v => node3463 (pivotPermutation3463 u) v) := by apply Matrix.ext; unfold pivotMatrix3463 node3463 pivotPermutation3463; decide +kernel
  have hmoment : injectiveMoment H node3463 = injectiveMoment H pivotMatrix3463 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3463 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3463 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3463 (0 : Fin 5)) =
      Sparse.eval value2014 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (0 : Fin 5) = raw7832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7832; decide +kernel
    rw [heq]
    exact (canonical7832 hH).trans (sound2014 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3463 (1 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (1 : Fin 5) = raw7801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7801; decide +kernel
    rw [heq]
    exact (canonical7801 hH).trans (sound1746 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3463 (2 : Fin 5)) =
      Sparse.eval value2840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (2 : Fin 5) = raw7794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7794; decide +kernel
    rw [heq]
    exact (canonical7794 hH).trans (sound2840 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3463 (3 : Fin 5)) =
      Sparse.eval value2839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (3 : Fin 5) = raw7792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7792; decide +kernel
    rw [heq]
    exact (canonical7792 hH).trans (sound2839 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3463 (4 : Fin 5)) =
      Sparse.eval value2839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (4 : Fin 5) = raw7791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7791; decide +kernel
    rw [heq]
    exact (canonical7791 hH).trans (sound2839 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3463 + (injectiveMoment H (mergeFirst pivotMatrix3463 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3463, value1746, value2014, value2839, value2840, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3464 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound3464 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3464 = Sparse.eval value3464 (momentVector H) := by
  have heq : pivotMatrix3464 = (fun u v => node3464 (pivotPermutation3464 u) v) := by apply Matrix.ext; unfold pivotMatrix3464 node3464 pivotPermutation3464; decide +kernel
  have hmoment : injectiveMoment H node3464 = injectiveMoment H pivotMatrix3464 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3464 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3464 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3464 (0 : Fin 5)) =
      Sparse.eval value2690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3464 (0 : Fin 5) = raw7192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3464 raw7192; decide +kernel
    rw [heq]
    exact (canonical7192 hH).trans (sound2690 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3464 (1 : Fin 5)) =
      Sparse.eval value2841 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3464 (1 : Fin 5) = raw7838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3464 raw7838; decide +kernel
    rw [heq]
    exact (canonical7838 hH).trans (sound2841 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3464 (2 : Fin 5)) =
      Sparse.eval value2841 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3464 (2 : Fin 5) = raw7849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3464 raw7849; decide +kernel
    rw [heq]
    exact (canonical7849 hH).trans (sound2841 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3464 (3 : Fin 5)) =
      Sparse.eval value2842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3464 (3 : Fin 5) = raw7850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3464 raw7850; decide +kernel
    rw [heq]
    exact (canonical7850 hH).trans (sound2842 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3464 (4 : Fin 5)) =
      Sparse.eval value2845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3464 (4 : Fin 5) = raw7853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3464 raw7853; decide +kernel
    rw [heq]
    exact (canonical7853 hH).trans (sound2845 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3464 + (injectiveMoment H (mergeFirst pivotMatrix3464 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3464 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3464 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3464 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3464 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3464, value2690, value2841, value2842, value2845, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3465 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3465 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem sound3465 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3465 = Sparse.eval value3465 (momentVector H) := by
  have heq : pivotMatrix3465 = (fun u v => node3465 (pivotPermutation3465 u) v) := by apply Matrix.ext; unfold pivotMatrix3465 node3465 pivotPermutation3465; decide +kernel
  have hmoment : injectiveMoment H node3465 = injectiveMoment H pivotMatrix3465 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3465 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3465 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3465 (0 : Fin 5)) =
      Sparse.eval value2836 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3465 (0 : Fin 5) = raw7777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3465 raw7777; decide +kernel
    rw [heq]
    exact (canonical7777 hH).trans (sound2836 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3465 (1 : Fin 5)) =
      Sparse.eval value2847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3465 (1 : Fin 5) = raw9061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3465 raw9061; decide +kernel
    rw [heq]
    exact (canonical9061 hH).trans (sound2847 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3465 (2 : Fin 5)) =
      Sparse.eval value2847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3465 (2 : Fin 5) = raw9071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3465 raw9071; decide +kernel
    rw [heq]
    exact (canonical9071 hH).trans (sound2847 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3465 (3 : Fin 5)) =
      Sparse.eval value2861 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3465 (3 : Fin 5) = raw9073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3465 raw9073; decide +kernel
    rw [heq]
    exact (canonical9073 hH).trans (sound2861 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3465 (4 : Fin 5)) =
      Sparse.eval value1293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3465 (4 : Fin 5) = raw9074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3465 raw9074; decide +kernel
    rw [heq]
    exact (canonical9074 hH).trans (sound1293 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3465 + (injectiveMoment H (mergeFirst pivotMatrix3465 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3465 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3465 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3465 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3465 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3465, value1293, value2836, value2847, value2861, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3466 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3466 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem sound3466 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3466 = Sparse.eval value3466 (momentVector H) := by
  have heq : pivotMatrix3466 = (fun u v => node3466 (pivotPermutation3466 u) v) := by apply Matrix.ext; unfold pivotMatrix3466 node3466 pivotPermutation3466; decide +kernel
  have hmoment : injectiveMoment H node3466 = injectiveMoment H pivotMatrix3466 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3466 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3466 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3466 (0 : Fin 5)) =
      Sparse.eval value2843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3466 (0 : Fin 5) = raw7851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3466 raw7851; decide +kernel
    rw [heq]
    exact (canonical7851 hH).trans (sound2843 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3466 (1 : Fin 5)) =
      Sparse.eval value2843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3466 (1 : Fin 5) = raw9194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3466 raw9194; decide +kernel
    rw [heq]
    exact (canonical9194 hH).trans (sound2843 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3466 (2 : Fin 5)) =
      Sparse.eval value2843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3466 (2 : Fin 5) = raw9244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3466 raw9244; decide +kernel
    rw [heq]
    exact (canonical9244 hH).trans (sound2843 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3466 (3 : Fin 5)) =
      Sparse.eval value2860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3466 (3 : Fin 5) = raw9260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3466 raw9260; decide +kernel
    rw [heq]
    exact (canonical9260 hH).trans (sound2860 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3466 (4 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3466 (4 : Fin 5) = raw9264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3466 raw9264; decide +kernel
    rw [heq]
    exact (canonical9264 hH).trans (sound884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3466 + (injectiveMoment H (mergeFirst pivotMatrix3466 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3466 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3466 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3466 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3466 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3466, value2843, value2860, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3467 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3467 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem sound3467 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3467 = Sparse.eval value3467 (momentVector H) := by
  have heq : pivotMatrix3467 = (fun u v => node3467 (pivotPermutation3467 u) v) := by apply Matrix.ext; unfold pivotMatrix3467 node3467 pivotPermutation3467; decide +kernel
  have hmoment : injectiveMoment H node3467 = injectiveMoment H pivotMatrix3467 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3467 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3467 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3467 (0 : Fin 5)) =
      Sparse.eval value2844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3467 (0 : Fin 5) = raw7852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3467 raw7852; decide +kernel
    rw [heq]
    exact (canonical7852 hH).trans (sound2844 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3467 (1 : Fin 5)) =
      Sparse.eval value2844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3467 (1 : Fin 5) = raw9195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3467 raw9195; decide +kernel
    rw [heq]
    exact (canonical9195 hH).trans (sound2844 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3467 (2 : Fin 5)) =
      Sparse.eval value2844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3467 (2 : Fin 5) = raw9245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3467 raw9245; decide +kernel
    rw [heq]
    exact (canonical9245 hH).trans (sound2844 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3467 (3 : Fin 5)) =
      Sparse.eval value2860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3467 (3 : Fin 5) = raw9261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3467 raw9261; decide +kernel
    rw [heq]
    exact (canonical9261 hH).trans (sound2860 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3467 (4 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3467 (4 : Fin 5) = raw9265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3467 raw9265; decide +kernel
    rw [heq]
    exact (canonical9265 hH).trans (sound884 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3467 + (injectiveMoment H (mergeFirst pivotMatrix3467 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3467 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3467 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3467 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3467 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3467, value2844, value2860, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3468 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3468 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem sound3468 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3468 = Sparse.eval value3468 (momentVector H) := by
  have heq : pivotMatrix3468 = (fun u v => node3468 (pivotPermutation3468 u) v) := by apply Matrix.ext; unfold pivotMatrix3468 node3468 pivotPermutation3468; decide +kernel
  have hmoment : injectiveMoment H node3468 = injectiveMoment H pivotMatrix3468 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3468 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3468 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3468 (0 : Fin 5)) =
      Sparse.eval value2845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3468 (0 : Fin 5) = raw7853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3468 raw7853; decide +kernel
    rw [heq]
    exact (canonical7853 hH).trans (sound2845 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3468 (1 : Fin 5)) =
      Sparse.eval value2845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3468 (1 : Fin 5) = raw9196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3468 raw9196; decide +kernel
    rw [heq]
    exact (canonical9196 hH).trans (sound2845 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3468 (2 : Fin 5)) =
      Sparse.eval value2845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3468 (2 : Fin 5) = raw9246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3468 raw9246; decide +kernel
    rw [heq]
    exact (canonical9246 hH).trans (sound2845 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3468 (3 : Fin 5)) =
      Sparse.eval value2862 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3468 (3 : Fin 5) = raw9262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3468 raw9262; decide +kernel
    rw [heq]
    exact (canonical9262 hH).trans (sound2862 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3468 (4 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3468 (4 : Fin 5) = raw9266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3468 raw9266; decide +kernel
    rw [heq]
    exact (canonical9266 hH).trans (sound748 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3468 + (injectiveMoment H (mergeFirst pivotMatrix3468 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3468 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3468 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3468 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3468 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3468, value2845, value2862, value748, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
