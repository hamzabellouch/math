import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1408 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1408 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

theorem sound1408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1408 = Sparse.eval value1408 (momentVector H) := by
  have heq : pivotMatrix1408 = (fun u v => node1408 (pivotPermutation1408 u) v) := by apply Matrix.ext; unfold pivotMatrix1408 node1408 pivotPermutation1408; decide +kernel
  have hmoment : injectiveMoment H node1408 = injectiveMoment H pivotMatrix1408 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1408 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1408 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1408 (0 : Fin 5)) =
      Sparse.eval value373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1408 (0 : Fin 5) = raw765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1408 raw765; decide +kernel
    rw [heq]
    exact (canonical765 hH).trans (sound373 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1408 (1 : Fin 5)) =
      Sparse.eval value344 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1408 (1 : Fin 5) = raw540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1408 raw540; decide +kernel
    rw [heq]
    exact (canonical540 hH).trans (sound344 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1408 (2 : Fin 5)) =
      Sparse.eval value344 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1408 (2 : Fin 5) = raw523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1408 raw523; decide +kernel
    rw [heq]
    exact (canonical523 hH).trans (sound344 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1408 (3 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1408 (3 : Fin 5) = raw517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1408 raw517; decide +kernel
    rw [heq]
    exact (canonical517 hH).trans (sound699 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1408 (4 : Fin 5)) =
      Sparse.eval value342 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1408 (4 : Fin 5) = raw516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1408 raw516; decide +kernel
    rw [heq]
    exact (canonical516 hH).trans (sound342 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1408 + (injectiveMoment H (mergeFirst pivotMatrix1408 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1408 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1408 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1408 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1408 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1408, value342, value344, value373, value699, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1409 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem sound1409 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1409 = Sparse.eval value1409 (momentVector H) := by
  have heq : pivotMatrix1409 = (fun u v => node1409 (pivotPermutation1409 u) v) := by apply Matrix.ext; unfold pivotMatrix1409 node1409 pivotPermutation1409; decide +kernel
  have hmoment : injectiveMoment H node1409 = injectiveMoment H pivotMatrix1409 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1409 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1409 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1409 (0 : Fin 5)) =
      Sparse.eval value374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1409 (0 : Fin 5) = raw767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1409 raw767; decide +kernel
    rw [heq]
    exact (canonical767 hH).trans (sound374 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1409 (1 : Fin 5)) =
      Sparse.eval value345 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1409 (1 : Fin 5) = raw541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1409 raw541; decide +kernel
    rw [heq]
    exact (canonical541 hH).trans (sound345 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1409 (2 : Fin 5)) =
      Sparse.eval value345 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1409 (2 : Fin 5) = raw524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1409 raw524; decide +kernel
    rw [heq]
    exact (canonical524 hH).trans (sound345 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1409 (3 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1409 (3 : Fin 5) = raw519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1409 raw519; decide +kernel
    rw [heq]
    exact (canonical519 hH).trans (sound1139 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1409 (4 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1409 (4 : Fin 5) = raw517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1409 raw517; decide +kernel
    rw [heq]
    exact (canonical517 hH).trans (sound699 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1409 + (injectiveMoment H (mergeFirst pivotMatrix1409 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1409 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1409 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1409 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1409 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1409, value1139, value345, value374, value699, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1410 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

theorem sound1410 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1410 = Sparse.eval value1410 (momentVector H) := by
  have heq : pivotMatrix1410 = (fun u v => node1410 (pivotPermutation1410 u) v) := by apply Matrix.ext; unfold pivotMatrix1410 node1410 pivotPermutation1410; decide +kernel
  have hmoment : injectiveMoment H node1410 = injectiveMoment H pivotMatrix1410 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1410 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1410 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1410 (0 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1410 (0 : Fin 5) = raw769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1410 raw769; decide +kernel
    rw [heq]
    exact (canonical769 hH).trans (sound573 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1410 (1 : Fin 5)) =
      Sparse.eval value346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1410 (1 : Fin 5) = raw542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1410 raw542; decide +kernel
    rw [heq]
    exact (canonical542 hH).trans (sound346 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1410 (2 : Fin 5)) =
      Sparse.eval value346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1410 (2 : Fin 5) = raw525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1410 raw525; decide +kernel
    rw [heq]
    exact (canonical525 hH).trans (sound346 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1410 (3 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1410 (3 : Fin 5) = raw520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1410 raw520; decide +kernel
    rw [heq]
    exact (canonical520 hH).trans (sound663 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1410 (4 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1410 (4 : Fin 5) = raw519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1410 raw519; decide +kernel
    rw [heq]
    exact (canonical519 hH).trans (sound1139 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1410 + (injectiveMoment H (mergeFirst pivotMatrix1410 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1410 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1410 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1410 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1410 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1410, value1139, value346, value573, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1411 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

theorem sound1411 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1411 = Sparse.eval value1411 (momentVector H) := by
  have heq : pivotMatrix1411 = (fun u v => node1411 (pivotPermutation1411 u) v) := by apply Matrix.ext; unfold pivotMatrix1411 node1411 pivotPermutation1411; decide +kernel
  have hmoment : injectiveMoment H node1411 = injectiveMoment H pivotMatrix1411 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1411 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1411 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1411 (0 : Fin 5)) =
      Sparse.eval value372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1411 (0 : Fin 5) = raw770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1411 raw770; decide +kernel
    rw [heq]
    exact (canonical770 hH).trans (sound372 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1411 (1 : Fin 5)) =
      Sparse.eval value347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1411 (1 : Fin 5) = raw543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1411 raw543; decide +kernel
    rw [heq]
    exact (canonical543 hH).trans (sound347 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1411 (2 : Fin 5)) =
      Sparse.eval value347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1411 (2 : Fin 5) = raw526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1411 raw526; decide +kernel
    rw [heq]
    exact (canonical526 hH).trans (sound347 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1411 (3 : Fin 5)) =
      Sparse.eval value343 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1411 (3 : Fin 5) = raw521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1411 raw521; decide +kernel
    rw [heq]
    exact (canonical521 hH).trans (sound343 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1411 (4 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1411 (4 : Fin 5) = raw520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1411 raw520; decide +kernel
    rw [heq]
    exact (canonical520 hH).trans (sound663 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1411 + (injectiveMoment H (mergeFirst pivotMatrix1411 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1411 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1411 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1411 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1411 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1411, value343, value347, value372, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1412 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

theorem sound1412 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1412 = Sparse.eval value1412 (momentVector H) := by
  have heq : pivotMatrix1412 = (fun u v => node1412 (pivotPermutation1412 u) v) := by apply Matrix.ext; unfold pivotMatrix1412 node1412 pivotPermutation1412; decide +kernel
  have hmoment : injectiveMoment H node1412 = injectiveMoment H pivotMatrix1412 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1412 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1412 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1412 (0 : Fin 5)) =
      Sparse.eval value373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1412 (0 : Fin 5) = raw785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1412 raw785; decide +kernel
    rw [heq]
    exact (canonical785 hH).trans (sound373 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1412 (1 : Fin 5)) =
      Sparse.eval value333 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1412 (1 : Fin 5) = raw557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1412 raw557; decide +kernel
    rw [heq]
    exact (canonical557 hH).trans (sound333 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1412 (2 : Fin 5)) =
      Sparse.eval value651 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1412 (2 : Fin 5) = raw549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1412 raw549; decide +kernel
    rw [heq]
    exact (canonical549 hH).trans (sound651 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1412 (3 : Fin 5)) =
      Sparse.eval value350 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1412 (3 : Fin 5) = raw546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1412 raw546; decide +kernel
    rw [heq]
    exact (canonical546 hH).trans (sound350 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1412 (4 : Fin 5)) =
      Sparse.eval value350 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1412 (4 : Fin 5) = raw545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1412 raw545; decide +kernel
    rw [heq]
    exact (canonical545 hH).trans (sound350 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1412 + (injectiveMoment H (mergeFirst pivotMatrix1412 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1412 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1412 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1412 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1412 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1412, value333, value350, value373, value651, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1413 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem sound1413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1413 = Sparse.eval value1413 (momentVector H) := by
  have heq : pivotMatrix1413 = (fun u v => node1413 (pivotPermutation1413 u) v) := by apply Matrix.ext; unfold pivotMatrix1413 node1413 pivotPermutation1413; decide +kernel
  have hmoment : injectiveMoment H node1413 = injectiveMoment H pivotMatrix1413 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1413 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1413 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1413 (0 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1413 (0 : Fin 5) = raw787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1413 raw787; decide +kernel
    rw [heq]
    exact (canonical787 hH).trans (sound377 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1413 (1 : Fin 5)) =
      Sparse.eval value339 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1413 (1 : Fin 5) = raw559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1413 raw559; decide +kernel
    rw [heq]
    exact (canonical559 hH).trans (sound339 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1413 (2 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1413 (2 : Fin 5) = raw551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1413 raw551; decide +kernel
    rw [heq]
    exact (canonical551 hH).trans (sound663 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1413 (3 : Fin 5)) =
      Sparse.eval value651 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1413 (3 : Fin 5) = raw549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1413 raw549; decide +kernel
    rw [heq]
    exact (canonical549 hH).trans (sound651 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1413 (4 : Fin 5)) =
      Sparse.eval value351 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1413 (4 : Fin 5) = raw548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1413 raw548; decide +kernel
    rw [heq]
    exact (canonical548 hH).trans (sound351 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1413 + (injectiveMoment H (mergeFirst pivotMatrix1413 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1413 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1413 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1413 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1413 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1413, value339, value351, value377, value651, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1414 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

theorem sound1414 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1414 = Sparse.eval value1414 (momentVector H) := by
  have heq : pivotMatrix1414 = (fun u v => node1414 (pivotPermutation1414 u) v) := by apply Matrix.ext; unfold pivotMatrix1414 node1414 pivotPermutation1414; decide +kernel
  have hmoment : injectiveMoment H node1414 = injectiveMoment H pivotMatrix1414 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1414 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1414 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1414 (0 : Fin 5)) =
      Sparse.eval value633 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1414 (0 : Fin 5) = raw464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1414 raw464; decide +kernel
    rw [heq]
    exact (canonical464 hH).trans (sound633 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1414 (1 : Fin 5)) =
      Sparse.eval value348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1414 (1 : Fin 5) = raw684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1414 raw684; decide +kernel
    rw [heq]
    exact (canonical684 hH).trans (sound348 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1414 (2 : Fin 5)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1414 (2 : Fin 5) = raw690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1414 raw690; decide +kernel
    rw [heq]
    exact (canonical690 hH).trans (sound209 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1414 (3 : Fin 5)) =
      Sparse.eval value355 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1414 (3 : Fin 5) = raw695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1414 raw695; decide +kernel
    rw [heq]
    exact (canonical695 hH).trans (sound355 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1414 (4 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1414 (4 : Fin 5) = raw697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1414 raw697; decide +kernel
    rw [heq]
    exact (canonical697 hH).trans (sound669 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1414 + (injectiveMoment H (mergeFirst pivotMatrix1414 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1414 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1414 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1414 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1414 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1414, value209, value348, value355, value633, value669, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1415 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

theorem sound1415 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1415 = Sparse.eval value1415 (momentVector H) := by
  have heq : pivotMatrix1415 = (fun u v => node1415 (pivotPermutation1415 u) v) := by apply Matrix.ext; unfold pivotMatrix1415 node1415 pivotPermutation1415; decide +kernel
  have hmoment : injectiveMoment H node1415 = injectiveMoment H pivotMatrix1415 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1415 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1415 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1415 (0 : Fin 5)) =
      Sparse.eval value631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1415 (0 : Fin 5) = raw468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1415 raw468; decide +kernel
    rw [heq]
    exact (canonical468 hH).trans (sound631 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1415 (1 : Fin 5)) =
      Sparse.eval value344 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1415 (1 : Fin 5) = raw685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1415 raw685; decide +kernel
    rw [heq]
    exact (canonical685 hH).trans (sound344 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1415 (2 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1415 (2 : Fin 5) = raw697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1415 raw697; decide +kernel
    rw [heq]
    exact (canonical697 hH).trans (sound669 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1415 (3 : Fin 5)) =
      Sparse.eval value357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1415 (3 : Fin 5) = raw701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1415 raw701; decide +kernel
    rw [heq]
    exact (canonical701 hH).trans (sound357 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1415 (4 : Fin 5)) =
      Sparse.eval value358 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1415 (4 : Fin 5) = raw702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1415 raw702; decide +kernel
    rw [heq]
    exact (canonical702 hH).trans (sound358 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1415 + (injectiveMoment H (mergeFirst pivotMatrix1415 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1415 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1415 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1415 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1415 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1415, value344, value357, value358, value631, value669, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1416 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

theorem sound1416 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1416 = Sparse.eval value1416 (momentVector H) := by
  have heq : pivotMatrix1416 = (fun u v => node1416 (pivotPermutation1416 u) v) := by apply Matrix.ext; unfold pivotMatrix1416 node1416 pivotPermutation1416; decide +kernel
  have hmoment : injectiveMoment H node1416 = injectiveMoment H pivotMatrix1416 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1416 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1416 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1416 (0 : Fin 5)) =
      Sparse.eval value551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1416 (0 : Fin 5) = raw479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1416 raw479; decide +kernel
    rw [heq]
    exact (canonical479 hH).trans (sound551 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1416 (1 : Fin 5)) =
      Sparse.eval value342 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1416 (1 : Fin 5) = raw686 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1416 raw686; decide +kernel
    rw [heq]
    exact (canonical686 hH).trans (sound342 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1416 (2 : Fin 5)) =
      Sparse.eval value360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1416 (2 : Fin 5) = raw706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1416 raw706; decide +kernel
    rw [heq]
    exact (canonical706 hH).trans (sound360 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1416 (3 : Fin 5)) =
      Sparse.eval value360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1416 (3 : Fin 5) = raw709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1416 raw709; decide +kernel
    rw [heq]
    exact (canonical709 hH).trans (sound360 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1416 (4 : Fin 5)) =
      Sparse.eval value666 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1416 (4 : Fin 5) = raw710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1416 raw710; decide +kernel
    rw [heq]
    exact (canonical710 hH).trans (sound666 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1416 + (injectiveMoment H (mergeFirst pivotMatrix1416 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1416 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1416 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1416 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1416 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1416, value342, value360, value551, value666, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1417 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem sound1417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1417 = Sparse.eval value1417 (momentVector H) := by
  have heq : pivotMatrix1417 = (fun u v => node1417 (pivotPermutation1417 u) v) := by apply Matrix.ext; unfold pivotMatrix1417 node1417 pivotPermutation1417; decide +kernel
  have hmoment : injectiveMoment H node1417 = injectiveMoment H pivotMatrix1417 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1417 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1417 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1417 (0 : Fin 5)) =
      Sparse.eval value369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1417 (0 : Fin 5) = raw826 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1417 raw826; decide +kernel
    rw [heq]
    exact (canonical826 hH).trans (sound369 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1417 (1 : Fin 5)) =
      Sparse.eval value869 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1417 (1 : Fin 5) = raw732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1417 raw732; decide +kernel
    rw [heq]
    exact (canonical732 hH).trans (sound869 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1417 (2 : Fin 5)) =
      Sparse.eval value357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1417 (2 : Fin 5) = raw701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1417 raw701; decide +kernel
    rw [heq]
    exact (canonical701 hH).trans (sound357 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1417 (3 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1417 (3 : Fin 5) = raw697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1417 raw697; decide +kernel
    rw [heq]
    exact (canonical697 hH).trans (sound669 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1417 (4 : Fin 5)) =
      Sparse.eval value355 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1417 (4 : Fin 5) = raw695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1417 raw695; decide +kernel
    rw [heq]
    exact (canonical695 hH).trans (sound355 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1417 + (injectiveMoment H (mergeFirst pivotMatrix1417 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1417 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1417 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1417 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1417 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1417, value355, value357, value369, value669, value869, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1418 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1418 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem sound1418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1418 = Sparse.eval value1418 (momentVector H) := by
  have heq : pivotMatrix1418 = (fun u v => node1418 (pivotPermutation1418 u) v) := by apply Matrix.ext; unfold pivotMatrix1418 node1418 pivotPermutation1418; decide +kernel
  have hmoment : injectiveMoment H node1418 = injectiveMoment H pivotMatrix1418 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1418 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1418 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1418 (0 : Fin 5)) =
      Sparse.eval value368 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1418 (0 : Fin 5) = raw827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1418 raw827; decide +kernel
    rw [heq]
    exact (canonical827 hH).trans (sound368 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1418 (1 : Fin 5)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1418 (1 : Fin 5) = raw733 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1418 raw733; decide +kernel
    rw [heq]
    exact (canonical733 hH).trans (sound868 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1418 (2 : Fin 5)) =
      Sparse.eval value358 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1418 (2 : Fin 5) = raw702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1418 raw702; decide +kernel
    rw [heq]
    exact (canonical702 hH).trans (sound358 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1418 (3 : Fin 5)) =
      Sparse.eval value356 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1418 (3 : Fin 5) = raw698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1418 raw698; decide +kernel
    rw [heq]
    exact (canonical698 hH).trans (sound356 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1418 (4 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1418 (4 : Fin 5) = raw697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1418 raw697; decide +kernel
    rw [heq]
    exact (canonical697 hH).trans (sound669 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1418 + (injectiveMoment H (mergeFirst pivotMatrix1418 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1418 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1418 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1418 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1418 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1418, value356, value358, value368, value669, value868, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1419 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1419 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem sound1419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1419 = Sparse.eval value1419 (momentVector H) := by
  have heq : pivotMatrix1419 = (fun u v => node1419 (pivotPermutation1419 u) v) := by apply Matrix.ext; unfold pivotMatrix1419 node1419 pivotPermutation1419; decide +kernel
  have hmoment : injectiveMoment H node1419 = injectiveMoment H pivotMatrix1419 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1419 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1419 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1419 (0 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1419 (0 : Fin 5) = raw829 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1419 raw829; decide +kernel
    rw [heq]
    exact (canonical829 hH).trans (sound377 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1419 (1 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1419 (1 : Fin 5) = raw747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1419 raw747; decide +kernel
    rw [heq]
    exact (canonical747 hH).trans (sound872 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1419 (2 : Fin 5)) =
      Sparse.eval value666 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1419 (2 : Fin 5) = raw710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1419 raw710; decide +kernel
    rw [heq]
    exact (canonical710 hH).trans (sound666 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1419 (3 : Fin 5)) =
      Sparse.eval value361 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1419 (3 : Fin 5) = raw707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1419 raw707; decide +kernel
    rw [heq]
    exact (canonical707 hH).trans (sound361 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1419 (4 : Fin 5)) =
      Sparse.eval value360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1419 (4 : Fin 5) = raw706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1419 raw706; decide +kernel
    rw [heq]
    exact (canonical706 hH).trans (sound360 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1419 + (injectiveMoment H (mergeFirst pivotMatrix1419 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1419 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1419 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1419 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1419 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1419, value360, value361, value377, value666, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1420 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1420 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound1420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1420 = Sparse.eval value1420 (momentVector H) := by
  have heq : pivotMatrix1420 = (fun u v => node1420 (pivotPermutation1420 u) v) := by apply Matrix.ext; unfold pivotMatrix1420 node1420 pivotPermutation1420; decide +kernel
  have hmoment : injectiveMoment H node1420 = injectiveMoment H pivotMatrix1420 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1420 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1420 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1420 (0 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1420 (0 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1420 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1420 (1 : Fin 5)) =
      Sparse.eval value373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1420 (1 : Fin 5) = raw796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1420 raw796; decide +kernel
    rw [heq]
    exact (canonical796 hH).trans (sound373 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1420 (2 : Fin 5)) =
      Sparse.eval value666 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1420 (2 : Fin 5) = raw712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1420 raw712; decide +kernel
    rw [heq]
    exact (canonical712 hH).trans (sound666 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1420 (3 : Fin 5)) =
      Sparse.eval value358 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1420 (3 : Fin 5) = raw703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1420 raw703; decide +kernel
    rw [heq]
    exact (canonical703 hH).trans (sound358 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1420 (4 : Fin 5)) =
      Sparse.eval value358 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1420 (4 : Fin 5) = raw702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1420 raw702; decide +kernel
    rw [heq]
    exact (canonical702 hH).trans (sound358 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1420 + (injectiveMoment H (mergeFirst pivotMatrix1420 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1420 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1420 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1420 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1420 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1420, value358, value373, value641, value666, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1421 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

theorem sound1421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1421 = Sparse.eval value1421 (momentVector H) := by
  have heq : pivotMatrix1421 = (fun u v => node1421 (pivotPermutation1421 u) v) := by apply Matrix.ext; unfold pivotMatrix1421 node1421 pivotPermutation1421; decide +kernel
  have hmoment : injectiveMoment H node1421 = injectiveMoment H pivotMatrix1421 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1421 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1421 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1421 (0 : Fin 5)) =
      Sparse.eval value1287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1421 (0 : Fin 5) = raw490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1421 raw490; decide +kernel
    rw [heq]
    exact (canonical490 hH).trans (sound1287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1421 (1 : Fin 5)) =
      Sparse.eval value354 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1421 (1 : Fin 5) = raw693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1421 raw693; decide +kernel
    rw [heq]
    exact (canonical693 hH).trans (sound354 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1421 (2 : Fin 5)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1421 (2 : Fin 5) = raw723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1421 raw723; decide +kernel
    rw [heq]
    exact (canonical723 hH).trans (sound259 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1421 (3 : Fin 5)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1421 (3 : Fin 5) = raw726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1421 raw726; decide +kernel
    rw [heq]
    exact (canonical726 hH).trans (sound259 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1421 (4 : Fin 5)) =
      Sparse.eval value364 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1421 (4 : Fin 5) = raw728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1421 raw728; decide +kernel
    rw [heq]
    exact (canonical728 hH).trans (sound364 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1421 + (injectiveMoment H (mergeFirst pivotMatrix1421 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1421 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1421 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1421 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1421 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1421, value1287, value259, value354, value364, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1422 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem sound1422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1422 = Sparse.eval value1422 (momentVector H) := by
  have heq : pivotMatrix1422 = (fun u v => node1422 (pivotPermutation1422 u) v) := by apply Matrix.ext; unfold pivotMatrix1422 node1422 pivotPermutation1422; decide +kernel
  have hmoment : injectiveMoment H node1422 = injectiveMoment H pivotMatrix1422 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1422 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1422 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1422 (0 : Fin 5)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1422 (0 : Fin 5) = raw493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1422 raw493; decide +kernel
    rw [heq]
    exact (canonical493 hH).trans (sound864 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1422 (1 : Fin 5)) =
      Sparse.eval value355 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1422 (1 : Fin 5) = raw695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1422 raw695; decide +kernel
    rw [heq]
    exact (canonical695 hH).trans (sound355 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1422 (2 : Fin 5)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1422 (2 : Fin 5) = raw724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1422 raw724; decide +kernel
    rw [heq]
    exact (canonical724 hH).trans (sound263 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1422 (3 : Fin 5)) =
      Sparse.eval value365 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1422 (3 : Fin 5) = raw729 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1422 raw729; decide +kernel
    rw [heq]
    exact (canonical729 hH).trans (sound365 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1422 (4 : Fin 5)) =
      Sparse.eval value869 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1422 (4 : Fin 5) = raw732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1422 raw732; decide +kernel
    rw [heq]
    exact (canonical732 hH).trans (sound869 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1422 + (injectiveMoment H (mergeFirst pivotMatrix1422 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1422 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1422 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1422 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1422 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1422, value263, value355, value365, value864, value869, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1423 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1423 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem sound1423 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1423 = Sparse.eval value1423 (momentVector H) := by
  have heq : pivotMatrix1423 = (fun u v => node1423 (pivotPermutation1423 u) v) := by apply Matrix.ext; unfold pivotMatrix1423 node1423 pivotPermutation1423; decide +kernel
  have hmoment : injectiveMoment H node1423 = injectiveMoment H pivotMatrix1423 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1423 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1423 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1423 (0 : Fin 5)) =
      Sparse.eval value1138 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1423 (0 : Fin 5) = raw494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1423 raw494; decide +kernel
    rw [heq]
    exact (canonical494 hH).trans (sound1138 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1423 (1 : Fin 5)) =
      Sparse.eval value356 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1423 (1 : Fin 5) = raw698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1423 raw698; decide +kernel
    rw [heq]
    exact (canonical698 hH).trans (sound356 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1423 (2 : Fin 5)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1423 (2 : Fin 5) = raw725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1423 raw725; decide +kernel
    rw [heq]
    exact (canonical725 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1423 (3 : Fin 5)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1423 (3 : Fin 5) = raw733 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1423 raw733; decide +kernel
    rw [heq]
    exact (canonical733 hH).trans (sound868 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1423 (4 : Fin 5)) =
      Sparse.eval value366 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1423 (4 : Fin 5) = raw734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1423 raw734; decide +kernel
    rw [heq]
    exact (canonical734 hH).trans (sound366 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1423 + (injectiveMoment H (mergeFirst pivotMatrix1423 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1423 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1423 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1423 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1423 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1423, value1138, value261, value356, value366, value868, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1424 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem sound1424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1424 = Sparse.eval value1424 (momentVector H) := by
  have heq : pivotMatrix1424 = (fun u v => node1424 (pivotPermutation1424 u) v) := by apply Matrix.ext; unfold pivotMatrix1424 node1424 pivotPermutation1424; decide +kernel
  have hmoment : injectiveMoment H node1424 = injectiveMoment H pivotMatrix1424 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1424 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1424 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1424 (0 : Fin 5)) =
      Sparse.eval value324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1424 (0 : Fin 5) = raw503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1424 raw503; decide +kernel
    rw [heq]
    exact (canonical503 hH).trans (sound324 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1424 (1 : Fin 5)) =
      Sparse.eval value359 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1424 (1 : Fin 5) = raw705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1424 raw705; decide +kernel
    rw [heq]
    exact (canonical705 hH).trans (sound359 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1424 (2 : Fin 5)) =
      Sparse.eval value370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1424 (2 : Fin 5) = raw742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1424 raw742; decide +kernel
    rw [heq]
    exact (canonical742 hH).trans (sound370 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1424 (3 : Fin 5)) =
      Sparse.eval value370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1424 (3 : Fin 5) = raw745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1424 raw745; decide +kernel
    rw [heq]
    exact (canonical745 hH).trans (sound370 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1424 (4 : Fin 5)) =
      Sparse.eval value372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1424 (4 : Fin 5) = raw746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1424 raw746; decide +kernel
    rw [heq]
    exact (canonical746 hH).trans (sound372 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1424 + (injectiveMoment H (mergeFirst pivotMatrix1424 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1424 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1424 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1424 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1424 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1424, value324, value359, value370, value372, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1425 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem sound1425 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1425 = Sparse.eval value1425 (momentVector H) := by
  have heq : pivotMatrix1425 = (fun u v => node1425 (pivotPermutation1425 u) v) := by apply Matrix.ext; unfold pivotMatrix1425 node1425 pivotPermutation1425; decide +kernel
  have hmoment : injectiveMoment H node1425 = injectiveMoment H pivotMatrix1425 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1425 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1425 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1425 (0 : Fin 5)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1425 (0 : Fin 5) = raw504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1425 raw504; decide +kernel
    rw [heq]
    exact (canonical504 hH).trans (sound563 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1425 (1 : Fin 5)) =
      Sparse.eval value360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1425 (1 : Fin 5) = raw706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1425 raw706; decide +kernel
    rw [heq]
    exact (canonical706 hH).trans (sound360 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1425 (2 : Fin 5)) =
      Sparse.eval value371 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1425 (2 : Fin 5) = raw743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1425 raw743; decide +kernel
    rw [heq]
    exact (canonical743 hH).trans (sound371 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1425 (3 : Fin 5)) =
      Sparse.eval value372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1425 (3 : Fin 5) = raw746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1425 raw746; decide +kernel
    rw [heq]
    exact (canonical746 hH).trans (sound372 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1425 (4 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1425 (4 : Fin 5) = raw747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1425 raw747; decide +kernel
    rw [heq]
    exact (canonical747 hH).trans (sound872 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1425 + (injectiveMoment H (mergeFirst pivotMatrix1425 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1425 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1425 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1425 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1425 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1425, value360, value371, value372, value563, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1426 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem sound1426 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1426 = Sparse.eval value1426 (momentVector H) := by
  have heq : pivotMatrix1426 = (fun u v => node1426 (pivotPermutation1426 u) v) := by apply Matrix.ext; unfold pivotMatrix1426 node1426 pivotPermutation1426; decide +kernel
  have hmoment : injectiveMoment H node1426 = injectiveMoment H pivotMatrix1426 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1426 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1426 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1426 (0 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1426 (0 : Fin 5) = raw517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1426 raw517; decide +kernel
    rw [heq]
    exact (canonical517 hH).trans (sound699 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1426 (1 : Fin 5)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1426 (1 : Fin 5) = raw752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1426 raw752; decide +kernel
    rw [heq]
    exact (canonical752 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1426 (2 : Fin 5)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1426 (2 : Fin 5) = raw760 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1426 raw760; decide +kernel
    rw [heq]
    exact (canonical760 hH).trans (sound226 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1426 (3 : Fin 5)) =
      Sparse.eval value373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1426 (3 : Fin 5) = raw765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1426 raw765; decide +kernel
    rw [heq]
    exact (canonical765 hH).trans (sound373 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1426 (4 : Fin 5)) =
      Sparse.eval value374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1426 (4 : Fin 5) = raw767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1426 raw767; decide +kernel
    rw [heq]
    exact (canonical767 hH).trans (sound374 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1426 + (injectiveMoment H (mergeFirst pivotMatrix1426 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1426 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1426 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1426 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1426 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1426, value226, value373, value374, value699, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1427 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem sound1427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1427 = Sparse.eval value1427 (momentVector H) := by
  have heq : pivotMatrix1427 = (fun u v => node1427 (pivotPermutation1427 u) v) := by apply Matrix.ext; unfold pivotMatrix1427 node1427 pivotPermutation1427; decide +kernel
  have hmoment : injectiveMoment H node1427 = injectiveMoment H pivotMatrix1427 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1427 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1427 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1427 (0 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1427 (0 : Fin 5) = raw519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1427 raw519; decide +kernel
    rw [heq]
    exact (canonical519 hH).trans (sound1139 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1427 (1 : Fin 5)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1427 (1 : Fin 5) = raw753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1427 raw753; decide +kernel
    rw [heq]
    exact (canonical753 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1427 (2 : Fin 5)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1427 (2 : Fin 5) = raw761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1427 raw761; decide +kernel
    rw [heq]
    exact (canonical761 hH).trans (sound181 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1427 (3 : Fin 5)) =
      Sparse.eval value374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1427 (3 : Fin 5) = raw767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1427 raw767; decide +kernel
    rw [heq]
    exact (canonical767 hH).trans (sound374 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1427 (4 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1427 (4 : Fin 5) = raw769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1427 raw769; decide +kernel
    rw [heq]
    exact (canonical769 hH).trans (sound573 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1427 + (injectiveMoment H (mergeFirst pivotMatrix1427 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1427 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1427 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1427 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1427 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1427, value1139, value181, value374, value573, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1428 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1428 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem sound1428 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1428 = Sparse.eval value1428 (momentVector H) := by
  have heq : pivotMatrix1428 = (fun u v => node1428 (pivotPermutation1428 u) v) := by apply Matrix.ext; unfold pivotMatrix1428 node1428 pivotPermutation1428; decide +kernel
  have hmoment : injectiveMoment H node1428 = injectiveMoment H pivotMatrix1428 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1428 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1428 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1428 (0 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1428 (0 : Fin 5) = raw520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1428 raw520; decide +kernel
    rw [heq]
    exact (canonical520 hH).trans (sound663 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1428 (1 : Fin 5)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1428 (1 : Fin 5) = raw754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1428 raw754; decide +kernel
    rw [heq]
    exact (canonical754 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1428 (2 : Fin 5)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1428 (2 : Fin 5) = raw762 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1428 raw762; decide +kernel
    rw [heq]
    exact (canonical762 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1428 (3 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1428 (3 : Fin 5) = raw769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1428 raw769; decide +kernel
    rw [heq]
    exact (canonical769 hH).trans (sound573 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1428 (4 : Fin 5)) =
      Sparse.eval value372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1428 (4 : Fin 5) = raw770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1428 raw770; decide +kernel
    rw [heq]
    exact (canonical770 hH).trans (sound372 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1428 + (injectiveMoment H (mergeFirst pivotMatrix1428 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1428 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1428 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1428 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1428 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1428, value185, value372, value573, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1429 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem sound1429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1429 = Sparse.eval value1429 (momentVector H) := by
  have heq : pivotMatrix1429 = (fun u v => node1429 (pivotPermutation1429 u) v) := by apply Matrix.ext; unfold pivotMatrix1429 node1429 pivotPermutation1429; decide +kernel
  have hmoment : injectiveMoment H node1429 = injectiveMoment H pivotMatrix1429 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1429 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1429 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1429 (0 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1429 (0 : Fin 5) = raw531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1429 raw531; decide +kernel
    rw [heq]
    exact (canonical531 hH).trans (sound697 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1429 (1 : Fin 5)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1429 (1 : Fin 5) = raw756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1429 raw756; decide +kernel
    rw [heq]
    exact (canonical756 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1429 (2 : Fin 5)) =
      Sparse.eval value375 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1429 (2 : Fin 5) = raw773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1429 raw773; decide +kernel
    rw [heq]
    exact (canonical773 hH).trans (sound375 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1429 (3 : Fin 5)) =
      Sparse.eval value376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1429 (3 : Fin 5) = raw776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1429 raw776; decide +kernel
    rw [heq]
    exact (canonical776 hH).trans (sound376 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1429 (4 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1429 (4 : Fin 5) = raw777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1429 raw777; decide +kernel
    rw [heq]
    exact (canonical777 hH).trans (sound708 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1429 + (injectiveMoment H (mergeFirst pivotMatrix1429 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1429 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1429 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1429 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1429 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1429, value229, value375, value376, value697, value708, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1430 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem sound1430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1430 = Sparse.eval value1430 (momentVector H) := by
  have heq : pivotMatrix1430 = (fun u v => node1430 (pivotPermutation1430 u) v) := by apply Matrix.ext; unfold pivotMatrix1430 node1430 pivotPermutation1430; decide +kernel
  have hmoment : injectiveMoment H node1430 = injectiveMoment H pivotMatrix1430 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1430 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1430 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1430 (0 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1430 (0 : Fin 5) = raw534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1430 raw534; decide +kernel
    rw [heq]
    exact (canonical534 hH).trans (sound1139 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1430 (1 : Fin 5)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1430 (1 : Fin 5) = raw758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1430 raw758; decide +kernel
    rw [heq]
    exact (canonical758 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1430 (2 : Fin 5)) =
      Sparse.eval value376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1430 (2 : Fin 5) = raw776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1430 raw776; decide +kernel
    rw [heq]
    exact (canonical776 hH).trans (sound376 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1430 (3 : Fin 5)) =
      Sparse.eval value376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1430 (3 : Fin 5) = raw779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1430 raw779; decide +kernel
    rw [heq]
    exact (canonical779 hH).trans (sound376 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1430 (4 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1430 (4 : Fin 5) = raw780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1430 raw780; decide +kernel
    rw [heq]
    exact (canonical780 hH).trans (sound570 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1430 + (injectiveMoment H (mergeFirst pivotMatrix1430 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1430 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1430 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1430 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1430 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1430, value1139, value176, value376, value570, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1431 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

theorem sound1431 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1431 = Sparse.eval value1431 (momentVector H) := by
  have heq : pivotMatrix1431 = (fun u v => node1431 (pivotPermutation1431 u) v) := by apply Matrix.ext; unfold pivotMatrix1431 node1431 pivotPermutation1431; decide +kernel
  have hmoment : injectiveMoment H node1431 = injectiveMoment H pivotMatrix1431 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1431 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1431 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1431 (0 : Fin 5)) =
      Sparse.eval value651 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1431 (0 : Fin 5) = raw549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1431 raw549; decide +kernel
    rw [heq]
    exact (canonical549 hH).trans (sound651 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1431 (1 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1431 (1 : Fin 5) = raw777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1431 raw777; decide +kernel
    rw [heq]
    exact (canonical777 hH).trans (sound708 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1431 (2 : Fin 5)) =
      Sparse.eval value373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1431 (2 : Fin 5) = raw785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1431 raw785; decide +kernel
    rw [heq]
    exact (canonical785 hH).trans (sound373 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1431 (3 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1431 (3 : Fin 5) = raw787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1431 raw787; decide +kernel
    rw [heq]
    exact (canonical787 hH).trans (sound377 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1431 (4 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1431 (4 : Fin 5) = raw788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1431 raw788; decide +kernel
    rw [heq]
    exact (canonical788 hH).trans (sound377 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1431 + (injectiveMoment H (mergeFirst pivotMatrix1431 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1431 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1431 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1431 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1431 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1431, value373, value377, value651, value708, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1432 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem sound1432 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1432 = Sparse.eval value1432 (momentVector H) := by
  have heq : pivotMatrix1432 = (fun u v => node1432 (pivotPermutation1432 u) v) := by apply Matrix.ext; unfold pivotMatrix1432 node1432 pivotPermutation1432; decide +kernel
  have hmoment : injectiveMoment H node1432 = injectiveMoment H pivotMatrix1432 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1432 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1432 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1432 (0 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1432 (0 : Fin 5) = raw551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1432 raw551; decide +kernel
    rw [heq]
    exact (canonical551 hH).trans (sound663 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1432 (1 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1432 (1 : Fin 5) = raw780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1432 raw780; decide +kernel
    rw [heq]
    exact (canonical780 hH).trans (sound570 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1432 (2 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1432 (2 : Fin 5) = raw787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1432 raw787; decide +kernel
    rw [heq]
    exact (canonical787 hH).trans (sound377 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1432 (3 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1432 (3 : Fin 5) = raw790 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1432 raw790; decide +kernel
    rw [heq]
    exact (canonical790 hH).trans (sound377 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1432 (4 : Fin 5)) =
      Sparse.eval value566 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1432 (4 : Fin 5) = raw791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1432 raw791; decide +kernel
    rw [heq]
    exact (canonical791 hH).trans (sound566 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1432 + (injectiveMoment H (mergeFirst pivotMatrix1432 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1432 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1432 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1432 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1432 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1432, value377, value566, value570, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1433 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

theorem sound1433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1433 = Sparse.eval value1433 (momentVector H) := by
  have heq : pivotMatrix1433 = (fun u v => node1433 (pivotPermutation1433 u) v) := by apply Matrix.ext; unfold pivotMatrix1433 node1433 pivotPermutation1433; decide +kernel
  have hmoment : injectiveMoment H node1433 = injectiveMoment H pivotMatrix1433 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1433 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1433 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1433 (0 : Fin 5)) =
      Sparse.eval value372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1433 (0 : Fin 5) = raw833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1433 raw833; decide +kernel
    rw [heq]
    exact (canonical833 hH).trans (sound372 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1433 (1 : Fin 5)) =
      Sparse.eval value373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1433 (1 : Fin 5) = raw785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1433 raw785; decide +kernel
    rw [heq]
    exact (canonical785 hH).trans (sound373 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1433 (2 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1433 (2 : Fin 5) = raw777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1433 raw777; decide +kernel
    rw [heq]
    exact (canonical777 hH).trans (sound708 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1433 (3 : Fin 5)) =
      Sparse.eval value375 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1433 (3 : Fin 5) = raw774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1433 raw774; decide +kernel
    rw [heq]
    exact (canonical774 hH).trans (sound375 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1433 (4 : Fin 5)) =
      Sparse.eval value375 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1433 (4 : Fin 5) = raw773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1433 raw773; decide +kernel
    rw [heq]
    exact (canonical773 hH).trans (sound375 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1433 + (injectiveMoment H (mergeFirst pivotMatrix1433 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1433 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1433 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1433 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1433 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1433, value372, value373, value375, value708, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1434 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem sound1434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1434 = Sparse.eval value1434 (momentVector H) := by
  have heq : pivotMatrix1434 = (fun u v => node1434 (pivotPermutation1434 u) v) := by apply Matrix.ext; unfold pivotMatrix1434 node1434 pivotPermutation1434; decide +kernel
  have hmoment : injectiveMoment H node1434 = injectiveMoment H pivotMatrix1434 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1434 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1434 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1434 (0 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1434 (0 : Fin 5) = raw835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1434 raw835; decide +kernel
    rw [heq]
    exact (canonical835 hH).trans (sound872 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1434 (1 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1434 (1 : Fin 5) = raw787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1434 raw787; decide +kernel
    rw [heq]
    exact (canonical787 hH).trans (sound377 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1434 (2 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1434 (2 : Fin 5) = raw780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1434 raw780; decide +kernel
    rw [heq]
    exact (canonical780 hH).trans (sound570 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1434 (3 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1434 (3 : Fin 5) = raw777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1434 raw777; decide +kernel
    rw [heq]
    exact (canonical777 hH).trans (sound708 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1434 (4 : Fin 5)) =
      Sparse.eval value376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1434 (4 : Fin 5) = raw776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1434 raw776; decide +kernel
    rw [heq]
    exact (canonical776 hH).trans (sound376 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1434 + (injectiveMoment H (mergeFirst pivotMatrix1434 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1434 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1434 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1434 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1434 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1434, value376, value377, value570, value708, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1435 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

theorem sound1435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1435 = Sparse.eval value1435 (momentVector H) := by
  have heq : pivotMatrix1435 = (fun u v => node1435 (pivotPermutation1435 u) v) := by apply Matrix.ext; unfold pivotMatrix1435 node1435 pivotPermutation1435; decide +kernel
  have hmoment : injectiveMoment H node1435 = injectiveMoment H pivotMatrix1435 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1435 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1435 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1435 (0 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1435 (0 : Fin 5) = raw697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1435 raw697; decide +kernel
    rw [heq]
    exact (canonical697 hH).trans (sound669 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1435 (1 : Fin 5)) =
      Sparse.eval value347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1435 (1 : Fin 5) = raw822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1435 raw822; decide +kernel
    rw [heq]
    exact (canonical822 hH).trans (sound347 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1435 (2 : Fin 5)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1435 (2 : Fin 5) = raw825 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1435 raw825; decide +kernel
    rw [heq]
    exact (canonical825 hH).trans (sound177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1435 (3 : Fin 5)) =
      Sparse.eval value369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1435 (3 : Fin 5) = raw826 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1435 raw826; decide +kernel
    rw [heq]
    exact (canonical826 hH).trans (sound369 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1435 (4 : Fin 5)) =
      Sparse.eval value368 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1435 (4 : Fin 5) = raw827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1435 raw827; decide +kernel
    rw [heq]
    exact (canonical827 hH).trans (sound368 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1435 + (injectiveMoment H (mergeFirst pivotMatrix1435 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1435 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1435 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1435 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1435 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1435, value177, value347, value368, value369, value669, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1436 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1436 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem sound1436 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1436 = Sparse.eval value1436 (momentVector H) := by
  have heq : pivotMatrix1436 = (fun u v => node1436 (pivotPermutation1436 u) v) := by apply Matrix.ext; unfold pivotMatrix1436 node1436 pivotPermutation1436; decide +kernel
  have hmoment : injectiveMoment H node1436 = injectiveMoment H pivotMatrix1436 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1436 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1436 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1436 (0 : Fin 5)) =
      Sparse.eval value437 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1436 (0 : Fin 5) = raw1398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1436 raw1398; decide +kernel
    rw [heq]
    exact (canonical1398 hH).trans (sound437 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1436 (1 : Fin 5)) =
      Sparse.eval value385 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1436 (1 : Fin 5) = raw947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1436 raw947; decide +kernel
    rw [heq]
    exact (canonical947 hH).trans (sound385 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1436 (2 : Fin 5)) =
      Sparse.eval value385 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1436 (2 : Fin 5) = raw937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1436 raw937; decide +kernel
    rw [heq]
    exact (canonical937 hH).trans (sound385 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1436 (3 : Fin 5)) =
      Sparse.eval value385 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1436 (3 : Fin 5) = raw932 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1436 raw932; decide +kernel
    rw [heq]
    exact (canonical932 hH).trans (sound385 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1436 (4 : Fin 5)) =
      Sparse.eval value384 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1436 (4 : Fin 5) = raw931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1436 raw931; decide +kernel
    rw [heq]
    exact (canonical931 hH).trans (sound384 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1436 + (injectiveMoment H (mergeFirst pivotMatrix1436 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1436 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1436 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1436 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1436 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1436, value384, value385, value437, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1437 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1437 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound1437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1437 = Sparse.eval value1437 (momentVector H) := by
  have heq : pivotMatrix1437 = (fun u v => node1437 (pivotPermutation1437 u) v) := by apply Matrix.ext; unfold pivotMatrix1437 node1437 pivotPermutation1437; decide +kernel
  have hmoment : injectiveMoment H node1437 = injectiveMoment H pivotMatrix1437 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1437 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1437 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1437 (0 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1437 (0 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1437 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1437 (1 : Fin 5)) =
      Sparse.eval value388 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1437 (1 : Fin 5) = raw948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1437 raw948; decide +kernel
    rw [heq]
    exact (canonical948 hH).trans (sound388 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1437 (2 : Fin 5)) =
      Sparse.eval value388 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1437 (2 : Fin 5) = raw938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1437 raw938; decide +kernel
    rw [heq]
    exact (canonical938 hH).trans (sound388 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1437 (3 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1437 (3 : Fin 5) = raw934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1437 raw934; decide +kernel
    rw [heq]
    exact (canonical934 hH).trans (sound387 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1437 (4 : Fin 5)) =
      Sparse.eval value386 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1437 (4 : Fin 5) = raw933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1437 raw933; decide +kernel
    rw [heq]
    exact (canonical933 hH).trans (sound386 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1437 + (injectiveMoment H (mergeFirst pivotMatrix1437 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1437 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1437 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1437 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1437 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1437, value386, value387, value388, value440, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1438 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound1438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1438 = Sparse.eval value1438 (momentVector H) := by
  have heq : pivotMatrix1438 = (fun u v => node1438 (pivotPermutation1438 u) v) := by apply Matrix.ext; unfold pivotMatrix1438 node1438 pivotPermutation1438; decide +kernel
  have hmoment : injectiveMoment H node1438 = injectiveMoment H pivotMatrix1438 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1438 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1438 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1438 (0 : Fin 5)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1438 (0 : Fin 5) = raw1402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1438 raw1402; decide +kernel
    rw [heq]
    exact (canonical1402 hH).trans (sound441 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1438 (1 : Fin 5)) =
      Sparse.eval value389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1438 (1 : Fin 5) = raw949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1438 raw949; decide +kernel
    rw [heq]
    exact (canonical949 hH).trans (sound389 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1438 (2 : Fin 5)) =
      Sparse.eval value389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1438 (2 : Fin 5) = raw939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1438 raw939; decide +kernel
    rw [heq]
    exact (canonical939 hH).trans (sound389 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1438 (3 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1438 (3 : Fin 5) = raw935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1438 raw935; decide +kernel
    rw [heq]
    exact (canonical935 hH).trans (sound387 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1438 (4 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1438 (4 : Fin 5) = raw934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1438 raw934; decide +kernel
    rw [heq]
    exact (canonical934 hH).trans (sound387 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1438 + (injectiveMoment H (mergeFirst pivotMatrix1438 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1438 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1438 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1438 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1438 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1438, value387, value389, value441, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1439 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1439 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem sound1439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1439 = Sparse.eval value1439 (momentVector H) := by
  have heq : pivotMatrix1439 = (fun u v => node1439 (pivotPermutation1439 u) v) := by apply Matrix.ext; unfold pivotMatrix1439 node1439 pivotPermutation1439; decide +kernel
  have hmoment : injectiveMoment H node1439 = injectiveMoment H pivotMatrix1439 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1439 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1439 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1439 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1439 (0 : Fin 4) = raw1058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1439 raw1058; decide +kernel
    rw [heq]
    exact (canonical1058 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1439 (1 : Fin 4)) =
      Sparse.eval value1258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1439 (1 : Fin 4) = raw984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1439 raw984; decide +kernel
    rw [heq]
    exact (canonical984 hH).trans (sound1258 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1439 (2 : Fin 4)) =
      Sparse.eval value890 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1439 (2 : Fin 4) = raw978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1439 raw978; decide +kernel
    rw [heq]
    exact (canonical978 hH).trans (sound890 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1439 (3 : Fin 4)) =
      Sparse.eval value1161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1439 (3 : Fin 4) = raw974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1439 raw974; decide +kernel
    rw [heq]
    exact (canonical974 hH).trans (sound1161 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1439 + (injectiveMoment H (mergeFirst pivotMatrix1439 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1439 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1439 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1439 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1439, value1161, value1178, value1258, value890, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1440 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1440 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem sound1440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1440 = Sparse.eval value1440 (momentVector H) := by
  have heq : pivotMatrix1440 = (fun u v => node1440 (pivotPermutation1440 u) v) := by apply Matrix.ext; unfold pivotMatrix1440 node1440 pivotPermutation1440; decide +kernel
  have hmoment : injectiveMoment H node1440 = injectiveMoment H pivotMatrix1440 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1440 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1440 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1440 (0 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1440 (0 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1440 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1440 (1 : Fin 4)) =
      Sparse.eval value753 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1440 (1 : Fin 4) = raw988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1440 raw988; decide +kernel
    rw [heq]
    exact (canonical988 hH).trans (sound753 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1440 (2 : Fin 4)) =
      Sparse.eval value752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1440 (2 : Fin 4) = raw980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1440 raw980; decide +kernel
    rw [heq]
    exact (canonical980 hH).trans (sound752 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1440 (3 : Fin 4)) =
      Sparse.eval value890 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1440 (3 : Fin 4) = raw978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1440 raw978; decide +kernel
    rw [heq]
    exact (canonical978 hH).trans (sound890 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1440 + (injectiveMoment H (mergeFirst pivotMatrix1440 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1440 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1440 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1440 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1440, value752, value753, value890, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1441 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1441 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem sound1441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1441 = Sparse.eval value1441 (momentVector H) := by
  have heq : pivotMatrix1441 = (fun u v => node1441 (pivotPermutation1441 u) v) := by apply Matrix.ext; unfold pivotMatrix1441 node1441 pivotPermutation1441; decide +kernel
  have hmoment : injectiveMoment H node1441 = injectiveMoment H pivotMatrix1441 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1441 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1441 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1441 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1441 (0 : Fin 4) = raw1121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1441 raw1121; decide +kernel
    rw [heq]
    exact (canonical1121 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1441 (1 : Fin 4)) =
      Sparse.eval value888 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1441 (1 : Fin 4) = raw1008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1441 raw1008; decide +kernel
    rw [heq]
    exact (canonical1008 hH).trans (sound888 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1441 (2 : Fin 4)) =
      Sparse.eval value1038 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1441 (2 : Fin 4) = raw1000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1441 raw1000; decide +kernel
    rw [heq]
    exact (canonical1000 hH).trans (sound1038 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1441 (3 : Fin 4)) =
      Sparse.eval value1030 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1441 (3 : Fin 4) = raw997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1441 raw997; decide +kernel
    rw [heq]
    exact (canonical997 hH).trans (sound1030 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1441 + (injectiveMoment H (mergeFirst pivotMatrix1441 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1441 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1441 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1441 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1441, value1030, value1031, value1038, value888, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1442 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1442 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound1442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1442 = Sparse.eval value1442 (momentVector H) := by
  have heq : pivotMatrix1442 = (fun u v => node1442 (pivotPermutation1442 u) v) := by apply Matrix.ext; unfold pivotMatrix1442 node1442 pivotPermutation1442; decide +kernel
  have hmoment : injectiveMoment H node1442 = injectiveMoment H pivotMatrix1442 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1442 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1442 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1442 (0 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1442 (0 : Fin 4) = raw1124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1442 raw1124; decide +kernel
    rw [heq]
    exact (canonical1124 hH).trans (sound1037 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1442 (1 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1442 (1 : Fin 4) = raw1010 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1442 raw1010; decide +kernel
    rw [heq]
    exact (canonical1010 hH).trans (sound751 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1442 (2 : Fin 4)) =
      Sparse.eval value1233 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1442 (2 : Fin 4) = raw1002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1442 raw1002; decide +kernel
    rw [heq]
    exact (canonical1002 hH).trans (sound1233 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1442 (3 : Fin 4)) =
      Sparse.eval value1038 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1442 (3 : Fin 4) = raw1000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1442 raw1000; decide +kernel
    rw [heq]
    exact (canonical1000 hH).trans (sound1038 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1442 + (injectiveMoment H (mergeFirst pivotMatrix1442 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1442 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1442 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1442 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1442, value1037, value1038, value1233, value751, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1443 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1443 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem sound1443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1443 = Sparse.eval value1443 (momentVector H) := by
  have heq : pivotMatrix1443 = (fun u v => node1443 (pivotPermutation1443 u) v) := by apply Matrix.ext; unfold pivotMatrix1443 node1443 pivotPermutation1443; decide +kernel
  have hmoment : injectiveMoment H node1443 = injectiveMoment H pivotMatrix1443 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1443 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1443 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1443 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1443 (0 : Fin 4) = raw1129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1443 raw1129; decide +kernel
    rw [heq]
    exact (canonical1129 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1443 (1 : Fin 4)) =
      Sparse.eval value889 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1443 (1 : Fin 4) = raw1012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1443 raw1012; decide +kernel
    rw [heq]
    exact (canonical1012 hH).trans (sound889 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1443 (2 : Fin 4)) =
      Sparse.eval value1240 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1443 (2 : Fin 4) = raw1004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1443 raw1004; decide +kernel
    rw [heq]
    exact (canonical1004 hH).trans (sound1240 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1443 (3 : Fin 4)) =
      Sparse.eval value1160 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1443 (3 : Fin 4) = raw1003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1443 raw1003; decide +kernel
    rw [heq]
    exact (canonical1003 hH).trans (sound1160 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1443 + (injectiveMoment H (mergeFirst pivotMatrix1443 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1443 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1443 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1443 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1443, value1160, value1168, value1240, value889, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1444 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1444 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem sound1444 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1444 = Sparse.eval value1444 (momentVector H) := by
  have heq : pivotMatrix1444 = (fun u v => node1444 (pivotPermutation1444 u) v) := by apply Matrix.ext; unfold pivotMatrix1444 node1444 pivotPermutation1444; decide +kernel
  have hmoment : injectiveMoment H node1444 = injectiveMoment H pivotMatrix1444 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1444 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1444 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1444 (0 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1444 (0 : Fin 4) = raw1130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1444 raw1130; decide +kernel
    rw [heq]
    exact (canonical1130 hH).trans (sound998 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1444 (1 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1444 (1 : Fin 4) = raw1013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1444 raw1013; decide +kernel
    rw [heq]
    exact (canonical1013 hH).trans (sound750 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1444 (2 : Fin 4)) =
      Sparse.eval value999 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1444 (2 : Fin 4) = raw1005 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1444 raw1005; decide +kernel
    rw [heq]
    exact (canonical1005 hH).trans (sound999 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1444 (3 : Fin 4)) =
      Sparse.eval value1240 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1444 (3 : Fin 4) = raw1004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1444 raw1004; decide +kernel
    rw [heq]
    exact (canonical1004 hH).trans (sound1240 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1444 + (injectiveMoment H (mergeFirst pivotMatrix1444 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1444 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1444 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1444 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1444, value1240, value750, value998, value999, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1445 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1445 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1445 = Sparse.eval value1445 (momentVector H) := by
  have heq : pivotMatrix1445 = (fun u v => node1445 (pivotPermutation1445 u) v) := by apply Matrix.ext; unfold pivotMatrix1445 node1445 pivotPermutation1445; decide +kernel
  have hmoment : injectiveMoment H node1445 = injectiveMoment H pivotMatrix1445 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1445 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1445 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1445 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1445 (0 : Fin 4) = raw1139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1445 raw1139; decide +kernel
    rw [heq]
    exact (canonical1139 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1445 (1 : Fin 4)) =
      Sparse.eval value392 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1445 (1 : Fin 4) = raw1019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1445 raw1019; decide +kernel
    rw [heq]
    exact (canonical1019 hH).trans (sound392 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1445 (2 : Fin 4)) =
      Sparse.eval value887 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1445 (2 : Fin 4) = raw1011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1445 raw1011; decide +kernel
    rw [heq]
    exact (canonical1011 hH).trans (sound887 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1445 (3 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1445 (3 : Fin 4) = raw1010 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1445 raw1010; decide +kernel
    rw [heq]
    exact (canonical1010 hH).trans (sound751 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1445 + (injectiveMoment H (mergeFirst pivotMatrix1445 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1445 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1445 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1445 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1445, value392, value751, value771, value887, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1446 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound1446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1446 = Sparse.eval value1446 (momentVector H) := by
  have heq : pivotMatrix1446 = (fun u v => node1446 (pivotPermutation1446 u) v) := by apply Matrix.ext; unfold pivotMatrix1446 node1446 pivotPermutation1446; decide +kernel
  have hmoment : injectiveMoment H node1446 = injectiveMoment H pivotMatrix1446 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1446 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1446 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1446 (0 : Fin 4)) =
      Sparse.eval value754 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1446 (0 : Fin 4) = raw1455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1446 raw1455; decide +kernel
    rw [heq]
    exact (canonical1455 hH).trans (sound754 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1446 (1 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1446 (1 : Fin 4) = raw1018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1446 raw1018; decide +kernel
    rw [heq]
    exact (canonical1018 hH).trans (sound751 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1446 (2 : Fin 4)) =
      Sparse.eval value391 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1446 (2 : Fin 4) = raw990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1446 raw990; decide +kernel
    rw [heq]
    exact (canonical990 hH).trans (sound391 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1446 (3 : Fin 4)) =
      Sparse.eval value753 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1446 (3 : Fin 4) = raw988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1446 raw988; decide +kernel
    rw [heq]
    exact (canonical988 hH).trans (sound753 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1446 + (injectiveMoment H (mergeFirst pivotMatrix1446 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1446 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1446 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1446 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1446, value391, value751, value753, value754, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1447 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1447 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1447 = Sparse.eval value1447 (momentVector H) := by
  have heq : pivotMatrix1447 = (fun u v => node1447 (pivotPermutation1447 u) v) := by apply Matrix.ext; unfold pivotMatrix1447 node1447 pivotPermutation1447; decide +kernel
  have hmoment : injectiveMoment H node1447 = injectiveMoment H pivotMatrix1447 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1447 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1447 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1447 (0 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1447 (0 : Fin 4) = raw1456 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1447 raw1456; decide +kernel
    rw [heq]
    exact (canonical1456 hH).trans (sound751 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1447 (1 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1447 (1 : Fin 4) = raw1020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1447 raw1020; decide +kernel
    rw [heq]
    exact (canonical1020 hH).trans (sound750 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1447 (2 : Fin 4)) =
      Sparse.eval value392 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1447 (2 : Fin 4) = raw993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1447 raw993; decide +kernel
    rw [heq]
    exact (canonical993 hH).trans (sound392 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1447 (3 : Fin 4)) =
      Sparse.eval value753 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1447 (3 : Fin 4) = raw992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1447 raw992; decide +kernel
    rw [heq]
    exact (canonical992 hH).trans (sound753 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1447 + (injectiveMoment H (mergeFirst pivotMatrix1447 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1447 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1447 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1447 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1447, value392, value750, value751, value753, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1448 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1448 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1448 = Sparse.eval value1448 (momentVector H) := by
  have heq : pivotMatrix1448 = (fun u v => node1448 (pivotPermutation1448 u) v) := by apply Matrix.ext; unfold pivotMatrix1448 node1448 pivotPermutation1448; decide +kernel
  have hmoment : injectiveMoment H node1448 = injectiveMoment H pivotMatrix1448 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1448 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1448 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1448 (0 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1448 (0 : Fin 4) = raw1627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1448 raw1627; decide +kernel
    rw [heq]
    exact (canonical1627 hH).trans (sound774 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1448 (1 : Fin 4)) =
      Sparse.eval value887 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1448 (1 : Fin 4) = raw1022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1448 raw1022; decide +kernel
    rw [heq]
    exact (canonical1022 hH).trans (sound887 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1448 (2 : Fin 4)) =
      Sparse.eval value391 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1448 (2 : Fin 4) = raw991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1448 raw991; decide +kernel
    rw [heq]
    exact (canonical991 hH).trans (sound391 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1448 (3 : Fin 4)) =
      Sparse.eval value753 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1448 (3 : Fin 4) = raw988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1448 raw988; decide +kernel
    rw [heq]
    exact (canonical988 hH).trans (sound753 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1448 + (injectiveMoment H (mergeFirst pivotMatrix1448 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1448 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1448 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1448 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1448, value391, value753, value774, value887, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1449 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1449 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1449 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1449 = Sparse.eval value1449 (momentVector H) := by
  have heq : pivotMatrix1449 = (fun u v => node1449 (pivotPermutation1449 u) v) := by apply Matrix.ext; unfold pivotMatrix1449 node1449 pivotPermutation1449; decide +kernel
  have hmoment : injectiveMoment H node1449 = injectiveMoment H pivotMatrix1449 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1449 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1449 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1449 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1449 (0 : Fin 4) = raw1642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1449 raw1642; decide +kernel
    rw [heq]
    exact (canonical1642 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1449 (1 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1449 (1 : Fin 4) = raw1023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1449 raw1023; decide +kernel
    rw [heq]
    exact (canonical1023 hH).trans (sound886 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1449 (2 : Fin 4)) =
      Sparse.eval value392 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1449 (2 : Fin 4) = raw994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1449 raw994; decide +kernel
    rw [heq]
    exact (canonical994 hH).trans (sound392 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1449 (3 : Fin 4)) =
      Sparse.eval value753 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1449 (3 : Fin 4) = raw992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1449 raw992; decide +kernel
    rw [heq]
    exact (canonical992 hH).trans (sound753 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1449 + (injectiveMoment H (mergeFirst pivotMatrix1449 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1449 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1449 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1449 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1449, value392, value753, value769, value886, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1450 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1450 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

theorem sound1450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1450 = Sparse.eval value1450 (momentVector H) := by
  have heq : pivotMatrix1450 = (fun u v => node1450 (pivotPermutation1450 u) v) := by apply Matrix.ext; unfold pivotMatrix1450 node1450 pivotPermutation1450; decide +kernel
  have hmoment : injectiveMoment H node1450 = injectiveMoment H pivotMatrix1450 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1450 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1450 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1450 (0 : Fin 4)) =
      Sparse.eval value890 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1450 (0 : Fin 4) = raw1457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1450 raw1457; decide +kernel
    rw [heq]
    exact (canonical1457 hH).trans (sound890 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1450 (1 : Fin 4)) =
      Sparse.eval value887 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1450 (1 : Fin 4) = raw1025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1450 raw1025; decide +kernel
    rw [heq]
    exact (canonical1025 hH).trans (sound887 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1450 (2 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1450 (2 : Fin 4) = raw1015 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1450 raw1015; decide +kernel
    rw [heq]
    exact (canonical1015 hH).trans (sound886 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1450 (3 : Fin 4)) =
      Sparse.eval value889 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1450 (3 : Fin 4) = raw1012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1450 raw1012; decide +kernel
    rw [heq]
    exact (canonical1012 hH).trans (sound889 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1450 + (injectiveMoment H (mergeFirst pivotMatrix1450 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1450 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1450 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1450 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1450, value886, value887, value889, value890, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1451 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1451 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

theorem sound1451 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1451 = Sparse.eval value1451 (momentVector H) := by
  have heq : pivotMatrix1451 = (fun u v => node1451 (pivotPermutation1451 u) v) := by apply Matrix.ext; unfold pivotMatrix1451 node1451 pivotPermutation1451; decide +kernel
  have hmoment : injectiveMoment H node1451 = injectiveMoment H pivotMatrix1451 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1451 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1451 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1451 (0 : Fin 4)) =
      Sparse.eval value755 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1451 (0 : Fin 4) = raw1458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1451 raw1458; decide +kernel
    rw [heq]
    exact (canonical1458 hH).trans (sound755 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1451 (1 : Fin 4)) =
      Sparse.eval value392 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1451 (1 : Fin 4) = raw1026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1451 raw1026; decide +kernel
    rw [heq]
    exact (canonical1026 hH).trans (sound392 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1451 (2 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1451 (2 : Fin 4) = raw1016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1451 raw1016; decide +kernel
    rw [heq]
    exact (canonical1016 hH).trans (sound750 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1451 (3 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1451 (3 : Fin 4) = raw1013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1451 raw1013; decide +kernel
    rw [heq]
    exact (canonical1013 hH).trans (sound750 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1451 + (injectiveMoment H (mergeFirst pivotMatrix1451 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1451 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1451 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1451 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1451, value392, value750, value755, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1452 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1452 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound1452 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1452 = Sparse.eval value1452 (momentVector H) := by
  have heq : pivotMatrix1452 = (fun u v => node1452 (pivotPermutation1452 u) v) := by apply Matrix.ext; unfold pivotMatrix1452 node1452 pivotPermutation1452; decide +kernel
  have hmoment : injectiveMoment H node1452 = injectiveMoment H pivotMatrix1452 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1452 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1452 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1452 (0 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1452 (0 : Fin 4) = raw1459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1452 raw1459; decide +kernel
    rw [heq]
    exact (canonical1459 hH).trans (sound750 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1452 (1 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1452 (1 : Fin 4) = raw1028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1452 raw1028; decide +kernel
    rw [heq]
    exact (canonical1028 hH).trans (sound751 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1452 (2 : Fin 4)) =
      Sparse.eval value393 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1452 (2 : Fin 4) = raw1021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1452 raw1021; decide +kernel
    rw [heq]
    exact (canonical1021 hH).trans (sound393 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1452 (3 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1452 (3 : Fin 4) = raw1020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1452 raw1020; decide +kernel
    rw [heq]
    exact (canonical1020 hH).trans (sound750 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1452 + (injectiveMoment H (mergeFirst pivotMatrix1452 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1452 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1452 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1452 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1452, value393, value750, value751, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1453 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1453 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound1453 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1453 = Sparse.eval value1453 (momentVector H) := by
  have heq : pivotMatrix1453 = (fun u v => node1453 (pivotPermutation1453 u) v) := by apply Matrix.ext; unfold pivotMatrix1453 node1453 pivotPermutation1453; decide +kernel
  have hmoment : injectiveMoment H node1453 = injectiveMoment H pivotMatrix1453 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1453 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1453 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1453 (0 : Fin 4)) =
      Sparse.eval value888 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1453 (0 : Fin 4) = raw1460 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1453 raw1460; decide +kernel
    rw [heq]
    exact (canonical1460 hH).trans (sound888 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1453 (1 : Fin 4)) =
      Sparse.eval value888 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1453 (1 : Fin 4) = raw1029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1453 raw1029; decide +kernel
    rw [heq]
    exact (canonical1029 hH).trans (sound888 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1453 (2 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1453 (2 : Fin 4) = raw1024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1453 raw1024; decide +kernel
    rw [heq]
    exact (canonical1024 hH).trans (sound886 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1453 (3 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1453 (3 : Fin 4) = raw1023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1453 raw1023; decide +kernel
    rw [heq]
    exact (canonical1023 hH).trans (sound886 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1453 + (injectiveMoment H (mergeFirst pivotMatrix1453 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1453 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1453 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1453 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1453, value886, value888, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1454 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1454 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem sound1454 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1454 = Sparse.eval value1454 (momentVector H) := by
  have heq : pivotMatrix1454 = (fun u v => node1454 (pivotPermutation1454 u) v) := by apply Matrix.ext; unfold pivotMatrix1454 node1454 pivotPermutation1454; decide +kernel
  have hmoment : injectiveMoment H node1454 = injectiveMoment H pivotMatrix1454 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1454 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1454 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1454 (0 : Fin 4)) =
      Sparse.eval value752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1454 (0 : Fin 4) = raw980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1454 raw980; decide +kernel
    rw [heq]
    exact (canonical980 hH).trans (sound752 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1454 (1 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1454 (1 : Fin 4) = raw1036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1454 raw1036; decide +kernel
    rw [heq]
    exact (canonical1036 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1454 (2 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1454 (2 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1454 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1454 (3 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1454 (3 : Fin 4) = raw1067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1454 raw1067; decide +kernel
    rw [heq]
    exact (canonical1067 hH).trans (sound772 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1454 + (injectiveMoment H (mergeFirst pivotMatrix1454 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1454 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1454 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1454 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1454, value153, value752, value772, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1455 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1455 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem sound1455 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1455 = Sparse.eval value1455 (momentVector H) := by
  have heq : pivotMatrix1455 = (fun u v => node1455 (pivotPermutation1455 u) v) := by apply Matrix.ext; unfold pivotMatrix1455 node1455 pivotPermutation1455; decide +kernel
  have hmoment : injectiveMoment H node1455 = injectiveMoment H pivotMatrix1455 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1455 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1455 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1455 (0 : Fin 4)) =
      Sparse.eval value1233 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1455 (0 : Fin 4) = raw1002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1455 raw1002; decide +kernel
    rw [heq]
    exact (canonical1002 hH).trans (sound1233 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1455 (1 : Fin 4)) =
      Sparse.eval value401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1455 (1 : Fin 4) = raw1109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1455 raw1109; decide +kernel
    rw [heq]
    exact (canonical1109 hH).trans (sound401 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1455 (2 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1455 (2 : Fin 4) = raw1124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1455 raw1124; decide +kernel
    rw [heq]
    exact (canonical1124 hH).trans (sound1037 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1455 (3 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1455 (3 : Fin 4) = raw1126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1455 raw1126; decide +kernel
    rw [heq]
    exact (canonical1126 hH).trans (sound1155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1455 + (injectiveMoment H (mergeFirst pivotMatrix1455 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1455 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1455 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1455 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1455, value1037, value1155, value1233, value401, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1456 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1456 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem sound1456 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1456 = Sparse.eval value1456 (momentVector H) := by
  have heq : pivotMatrix1456 = (fun u v => node1456 (pivotPermutation1456 u) v) := by apply Matrix.ext; unfold pivotMatrix1456 node1456 pivotPermutation1456; decide +kernel
  have hmoment : injectiveMoment H node1456 = injectiveMoment H pivotMatrix1456 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1456 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1456 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1456 (0 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1456 (0 : Fin 4) = raw1014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1456 raw1014; decide +kernel
    rw [heq]
    exact (canonical1014 hH).trans (sound886 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1456 (1 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1456 (1 : Fin 4) = raw1131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1456 raw1131; decide +kernel
    rw [heq]
    exact (canonical1131 hH).trans (sound996 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1456 (2 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1456 (2 : Fin 4) = raw1143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1456 raw1143; decide +kernel
    rw [heq]
    exact (canonical1143 hH).trans (sound786 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1456 (3 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1456 (3 : Fin 4) = raw1144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1456 raw1144; decide +kernel
    rw [heq]
    exact (canonical1144 hH).trans (sound997 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1456 + (injectiveMoment H (mergeFirst pivotMatrix1456 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1456 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1456 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1456 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1456, value786, value886, value996, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1457 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1457 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem sound1457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1457 = Sparse.eval value1457 (momentVector H) := by
  have heq : pivotMatrix1457 = (fun u v => node1457 (pivotPermutation1457 u) v) := by apply Matrix.ext; unfold pivotMatrix1457 node1457 pivotPermutation1457; decide +kernel
  have hmoment : injectiveMoment H node1457 = injectiveMoment H pivotMatrix1457 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1457 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1457 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1457 (0 : Fin 4)) =
      Sparse.eval value1329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1457 (0 : Fin 4) = raw1206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1457 raw1206; decide +kernel
    rw [heq]
    exact (canonical1206 hH).trans (sound1329 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1457 (1 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1457 (1 : Fin 4) = raw1082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1457 raw1082; decide +kernel
    rw [heq]
    exact (canonical1082 hH).trans (sound394 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1457 (2 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1457 (2 : Fin 4) = raw1058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1457 raw1058; decide +kernel
    rw [heq]
    exact (canonical1058 hH).trans (sound1178 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1457 (3 : Fin 4)) =
      Sparse.eval value1325 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1457 (3 : Fin 4) = raw1051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1457 raw1051; decide +kernel
    rw [heq]
    exact (canonical1051 hH).trans (sound1325 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1457 + (injectiveMoment H (mergeFirst pivotMatrix1457 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1457 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1457 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1457 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1457, value1178, value1325, value1329, value394, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1458 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1458 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem sound1458 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1458 = Sparse.eval value1458 (momentVector H) := by
  have heq : pivotMatrix1458 = (fun u v => node1458 (pivotPermutation1458 u) v) := by apply Matrix.ext; unfold pivotMatrix1458 node1458 pivotPermutation1458; decide +kernel
  have hmoment : injectiveMoment H node1458 = injectiveMoment H pivotMatrix1458 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1458 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1458 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1458 (0 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1458 (0 : Fin 4) = raw1211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1458 raw1211; decide +kernel
    rw [heq]
    exact (canonical1211 hH).trans (sound1222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1458 (1 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1458 (1 : Fin 4) = raw1088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1458 raw1088; decide +kernel
    rw [heq]
    exact (canonical1088 hH).trans (sound1257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1458 (2 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1458 (2 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1458 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1458 (3 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1458 (3 : Fin 4) = raw1058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1458 raw1058; decide +kernel
    rw [heq]
    exact (canonical1058 hH).trans (sound1178 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1458 + (injectiveMoment H (mergeFirst pivotMatrix1458 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1458 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1458 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1458 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1458, value1178, value1222, value1257, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1459 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1459 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem sound1459 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1459 = Sparse.eval value1459 (momentVector H) := by
  have heq : pivotMatrix1459 = (fun u v => node1459 (pivotPermutation1459 u) v) := by apply Matrix.ext; unfold pivotMatrix1459 node1459 pivotPermutation1459; decide +kernel
  have hmoment : injectiveMoment H node1459 = injectiveMoment H pivotMatrix1459 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1459 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1459 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1459 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (0 : Fin 4) = raw1216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1216; decide +kernel
    rw [heq]
    exact (canonical1216 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1459 (1 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (1 : Fin 4) = raw1092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1092; decide +kernel
    rw [heq]
    exact (canonical1092 hH).trans (sound773 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1459 (2 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (2 : Fin 4) = raw1067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1067; decide +kernel
    rw [heq]
    exact (canonical1067 hH).trans (sound772 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1459 (3 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1459 (3 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1459 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1459 + (injectiveMoment H (mergeFirst pivotMatrix1459 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1459 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1459 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1459 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1459, value772, value773, value914, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1460 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1460 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem sound1460 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1460 = Sparse.eval value1460 (momentVector H) := by
  have heq : pivotMatrix1460 = (fun u v => node1460 (pivotPermutation1460 u) v) := by apply Matrix.ext; unfold pivotMatrix1460 node1460 pivotPermutation1460; decide +kernel
  have hmoment : injectiveMoment H node1460 = injectiveMoment H pivotMatrix1460 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1460 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1460 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1460 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1460 (0 : Fin 4) = raw1218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1460 raw1218; decide +kernel
    rw [heq]
    exact (canonical1218 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1460 (1 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1460 (1 : Fin 4) = raw1094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1460 raw1094; decide +kernel
    rw [heq]
    exact (canonical1094 hH).trans (sound395 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1460 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1460 (2 : Fin 4) = raw1072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1460 raw1072; decide +kernel
    rw [heq]
    exact (canonical1072 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1460 (3 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1460 (3 : Fin 4) = raw1069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1460 raw1069; decide +kernel
    rw [heq]
    exact (canonical1069 hH).trans (sound1180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1460 + (injectiveMoment H (mergeFirst pivotMatrix1460 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1460 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1460 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1460 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1460, value1180, value395, value775, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1461 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1461 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem sound1461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1461 = Sparse.eval value1461 (momentVector H) := by
  have heq : pivotMatrix1461 = (fun u v => node1461 (pivotPermutation1461 u) v) := by apply Matrix.ext; unfold pivotMatrix1461 node1461 pivotPermutation1461; decide +kernel
  have hmoment : injectiveMoment H node1461 = injectiveMoment H pivotMatrix1461 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1461 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1461 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1461 (0 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1461 (0 : Fin 4) = raw1220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1461 raw1220; decide +kernel
    rw [heq]
    exact (canonical1220 hH).trans (sound976 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1461 (1 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1461 (1 : Fin 4) = raw1096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1461 raw1096; decide +kernel
    rw [heq]
    exact (canonical1096 hH).trans (sound396 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1461 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1461 (2 : Fin 4) = raw1074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1461 raw1074; decide +kernel
    rw [heq]
    exact (canonical1074 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1461 (3 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1461 (3 : Fin 4) = raw1072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1461 raw1072; decide +kernel
    rw [heq]
    exact (canonical1072 hH).trans (sound775 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1461 + (injectiveMoment H (mergeFirst pivotMatrix1461 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1461 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1461 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1461 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1461, value396, value775, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1462 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1462 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem sound1462 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1462 = Sparse.eval value1462 (momentVector H) := by
  have heq : pivotMatrix1462 = (fun u v => node1462 (pivotPermutation1462 u) v) := by apply Matrix.ext; unfold pivotMatrix1462 node1462 pivotPermutation1462; decide +kernel
  have hmoment : injectiveMoment H node1462 = injectiveMoment H pivotMatrix1462 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1462 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1462 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1462 (0 : Fin 4)) =
      Sparse.eval value820 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1462 (0 : Fin 4) = raw1225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1462 raw1225; decide +kernel
    rw [heq]
    exact (canonical1225 hH).trans (sound820 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1462 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1462 (1 : Fin 4) = raw1101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1462 raw1101; decide +kernel
    rw [heq]
    exact (canonical1101 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1462 (2 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1462 (2 : Fin 4) = raw1079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1462 raw1079; decide +kernel
    rw [heq]
    exact (canonical1079 hH).trans (sound787 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1462 (3 : Fin 4)) =
      Sparse.eval value1186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1462 (3 : Fin 4) = raw1078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1462 raw1078; decide +kernel
    rw [heq]
    exact (canonical1078 hH).trans (sound1186 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1462 + (injectiveMoment H (mergeFirst pivotMatrix1462 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1462 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1462 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1462 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1462, value1186, value397, value787, value820, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1463 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1463 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem sound1463 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1463 = Sparse.eval value1463 (momentVector H) := by
  have heq : pivotMatrix1463 = (fun u v => node1463 (pivotPermutation1463 u) v) := by apply Matrix.ext; unfold pivotMatrix1463 node1463 pivotPermutation1463; decide +kernel
  have hmoment : injectiveMoment H node1463 = injectiveMoment H pivotMatrix1463 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1463 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1463 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1463 (0 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (0 : Fin 4) = raw1231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1231; decide +kernel
    rw [heq]
    exact (canonical1231 hH).trans (sound1035 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1463 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (1 : Fin 4) = raw1121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1121; decide +kernel
    rw [heq]
    exact (canonical1121 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1463 (2 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (2 : Fin 4) = raw1107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1107; decide +kernel
    rw [heq]
    exact (canonical1107 hH).trans (sound400 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1463 (3 : Fin 4)) =
      Sparse.eval value1034 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1463 (3 : Fin 4) = raw1104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1463 raw1104; decide +kernel
    rw [heq]
    exact (canonical1104 hH).trans (sound1034 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1463 + (injectiveMoment H (mergeFirst pivotMatrix1463 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1463 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1463 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1463 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1463, value1031, value1034, value1035, value400, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1464 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1464 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound1464 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1464 = Sparse.eval value1464 (momentVector H) := by
  have heq : pivotMatrix1464 = (fun u v => node1464 (pivotPermutation1464 u) v) := by apply Matrix.ext; unfold pivotMatrix1464 node1464 pivotPermutation1464; decide +kernel
  have hmoment : injectiveMoment H node1464 = injectiveMoment H pivotMatrix1464 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1464 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1464 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1464 (0 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1464 (0 : Fin 4) = raw1233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1464 raw1233; decide +kernel
    rw [heq]
    exact (canonical1233 hH).trans (sound408 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1464 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1464 (1 : Fin 4) = raw1124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1464 raw1124; decide +kernel
    rw [heq]
    exact (canonical1124 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1464 (2 : Fin 4)) =
      Sparse.eval value401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1464 (2 : Fin 4) = raw1109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1464 raw1109; decide +kernel
    rw [heq]
    exact (canonical1109 hH).trans (sound401 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1464 (3 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1464 (3 : Fin 4) = raw1107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1464 raw1107; decide +kernel
    rw [heq]
    exact (canonical1107 hH).trans (sound400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1464 + (injectiveMoment H (mergeFirst pivotMatrix1464 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1464 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1464 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1464 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1464, value1037, value400, value401, value408, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1465 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1465 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem sound1465 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1465 = Sparse.eval value1465 (momentVector H) := by
  have heq : pivotMatrix1465 = (fun u v => node1465 (pivotPermutation1465 u) v) := by apply Matrix.ext; unfold pivotMatrix1465 node1465 pivotPermutation1465; decide +kernel
  have hmoment : injectiveMoment H node1465 = injectiveMoment H pivotMatrix1465 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1465 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1465 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1465 (0 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1465 (0 : Fin 4) = raw1235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1465 raw1235; decide +kernel
    rw [heq]
    exact (canonical1235 hH).trans (sound1239 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1465 (1 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1465 (1 : Fin 4) = raw1129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1465 raw1129; decide +kernel
    rw [heq]
    exact (canonical1129 hH).trans (sound1168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1465 (2 : Fin 4)) =
      Sparse.eval value402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1465 (2 : Fin 4) = raw1111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1465 raw1111; decide +kernel
    rw [heq]
    exact (canonical1111 hH).trans (sound402 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1465 (3 : Fin 4)) =
      Sparse.eval value1238 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1465 (3 : Fin 4) = raw1110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1465 raw1110; decide +kernel
    rw [heq]
    exact (canonical1110 hH).trans (sound1238 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1465 + (injectiveMoment H (mergeFirst pivotMatrix1465 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1465 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1465 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1465 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1465, value1168, value1238, value1239, value402, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1466 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1466 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem sound1466 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1466 = Sparse.eval value1466 (momentVector H) := by
  have heq : pivotMatrix1466 = (fun u v => node1466 (pivotPermutation1466 u) v) := by apply Matrix.ext; unfold pivotMatrix1466 node1466 pivotPermutation1466; decide +kernel
  have hmoment : injectiveMoment H node1466 = injectiveMoment H pivotMatrix1466 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1466 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1466 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1466 (0 : Fin 4)) =
      Sparse.eval value409 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1466 (0 : Fin 4) = raw1236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1466 raw1236; decide +kernel
    rw [heq]
    exact (canonical1236 hH).trans (sound409 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1466 (1 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1466 (1 : Fin 4) = raw1130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1466 raw1130; decide +kernel
    rw [heq]
    exact (canonical1130 hH).trans (sound998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1466 (2 : Fin 4)) =
      Sparse.eval value403 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1466 (2 : Fin 4) = raw1112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1466 raw1112; decide +kernel
    rw [heq]
    exact (canonical1112 hH).trans (sound403 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1466 (3 : Fin 4)) =
      Sparse.eval value402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1466 (3 : Fin 4) = raw1111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1466 raw1111; decide +kernel
    rw [heq]
    exact (canonical1111 hH).trans (sound402 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1466 + (injectiveMoment H (mergeFirst pivotMatrix1466 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1466 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1466 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1466 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1466, value402, value403, value409, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1467 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1467 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

theorem sound1467 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1467 = Sparse.eval value1467 (momentVector H) := by
  have heq : pivotMatrix1467 = (fun u v => node1467 (pivotPermutation1467 u) v) := by apply Matrix.ext; unfold pivotMatrix1467 node1467 pivotPermutation1467; decide +kernel
  have hmoment : injectiveMoment H node1467 = injectiveMoment H pivotMatrix1467 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1467 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1467 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1467 (0 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1467 (0 : Fin 4) = raw1242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1467 raw1242; decide +kernel
    rw [heq]
    exact (canonical1242 hH).trans (sound1028 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1467 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1467 (1 : Fin 4) = raw1136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1467 raw1136; decide +kernel
    rw [heq]
    exact (canonical1136 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1467 (2 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1467 (2 : Fin 4) = raw1121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1467 raw1121; decide +kernel
    rw [heq]
    exact (canonical1121 hH).trans (sound1031 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1467 (3 : Fin 4)) =
      Sparse.eval value1029 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1467 (3 : Fin 4) = raw1118 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1467 raw1118; decide +kernel
    rw [heq]
    exact (canonical1118 hH).trans (sound1029 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1467 + (injectiveMoment H (mergeFirst pivotMatrix1467 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1467 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1467 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1467 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1467, value1028, value1029, value1031, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1468 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1468 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1468 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1468 = Sparse.eval value1468 (momentVector H) := by
  have heq : pivotMatrix1468 = (fun u v => node1468 (pivotPermutation1468 u) v) := by apply Matrix.ext; unfold pivotMatrix1468 node1468 pivotPermutation1468; decide +kernel
  have hmoment : injectiveMoment H node1468 = injectiveMoment H pivotMatrix1468 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1468 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1468 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1468 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1468 (0 : Fin 4) = raw1248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1468 raw1248; decide +kernel
    rw [heq]
    exact (canonical1248 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1468 (1 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1468 (1 : Fin 4) = raw1139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1468 raw1139; decide +kernel
    rw [heq]
    exact (canonical1139 hH).trans (sound771 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1468 (2 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1468 (2 : Fin 4) = raw1126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1468 raw1126; decide +kernel
    rw [heq]
    exact (canonical1126 hH).trans (sound1155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1468 (3 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1468 (3 : Fin 4) = raw1124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1468 raw1124; decide +kernel
    rw [heq]
    exact (canonical1124 hH).trans (sound1037 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1468 + (injectiveMoment H (mergeFirst pivotMatrix1468 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1468 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1468 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1468 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1468, value1036, value1037, value1155, value771, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1469 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1469 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound1469 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1469 = Sparse.eval value1469 (momentVector H) := by
  have heq : pivotMatrix1469 = (fun u v => node1469 (pivotPermutation1469 u) v) := by apply Matrix.ext; unfold pivotMatrix1469 node1469 pivotPermutation1469; decide +kernel
  have hmoment : injectiveMoment H node1469 = injectiveMoment H pivotMatrix1469 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1469 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1469 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1469 (0 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1469 (0 : Fin 4) = raw1250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1469 raw1250; decide +kernel
    rw [heq]
    exact (canonical1250 hH).trans (sound1104 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1469 (1 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1469 (1 : Fin 4) = raw1142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1469 raw1142; decide +kernel
    rw [heq]
    exact (canonical1142 hH).trans (sound1168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1469 (2 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1469 (2 : Fin 4) = raw1129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1469 raw1129; decide +kernel
    rw [heq]
    exact (canonical1129 hH).trans (sound1168 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1469 (3 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1469 (3 : Fin 4) = raw1128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1469 raw1128; decide +kernel
    rw [heq]
    exact (canonical1128 hH).trans (sound1070 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1469 + (injectiveMoment H (mergeFirst pivotMatrix1469 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1469 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1469 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1469 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1469, value1070, value1104, value1168, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1470 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1470 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound1470 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1470 = Sparse.eval value1470 (momentVector H) := by
  have heq : pivotMatrix1470 = (fun u v => node1470 (pivotPermutation1470 u) v) := by apply Matrix.ext; unfold pivotMatrix1470 node1470 pivotPermutation1470; decide +kernel
  have hmoment : injectiveMoment H node1470 = injectiveMoment H pivotMatrix1470 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1470 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1470 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1470 (0 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1470 (0 : Fin 4) = raw1252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1470 raw1252; decide +kernel
    rw [heq]
    exact (canonical1252 hH).trans (sound995 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1470 (1 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1470 (1 : Fin 4) = raw1143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1470 raw1143; decide +kernel
    rw [heq]
    exact (canonical1143 hH).trans (sound786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1470 (2 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1470 (2 : Fin 4) = raw1131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1470 raw1131; decide +kernel
    rw [heq]
    exact (canonical1131 hH).trans (sound996 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1470 (3 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1470 (3 : Fin 4) = raw1130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1470 raw1130; decide +kernel
    rw [heq]
    exact (canonical1130 hH).trans (sound998 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1470 + (injectiveMoment H (mergeFirst pivotMatrix1470 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1470 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1470 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1470 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1470, value786, value995, value996, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1471 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1471 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem sound1471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1471 = Sparse.eval value1471 (momentVector H) := by
  have heq : pivotMatrix1471 = (fun u v => node1471 (pivotPermutation1471 u) v) := by apply Matrix.ext; unfold pivotMatrix1471 node1471 pivotPermutation1471; decide +kernel
  have hmoment : injectiveMoment H node1471 = injectiveMoment H pivotMatrix1471 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1471 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1471 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1471 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (0 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1471 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (1 : Fin 4) = raw1150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1150; decide +kernel
    rw [heq]
    exact (canonical1150 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1471 (2 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (2 : Fin 4) = raw1141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1141; decide +kernel
    rw [heq]
    exact (canonical1141 hH).trans (sound1164 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1471 (3 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1471 (3 : Fin 4) = raw1139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1471 raw1139; decide +kernel
    rw [heq]
    exact (canonical1139 hH).trans (sound771 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1471 + (injectiveMoment H (mergeFirst pivotMatrix1471 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1471 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1471 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1471 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1471, value1164, value397, value771, value804, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
