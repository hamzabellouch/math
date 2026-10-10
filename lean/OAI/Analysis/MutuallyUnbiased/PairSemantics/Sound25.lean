import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical57
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1600 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1600 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound1600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1600 = Sparse.eval value1600 (momentVector H) := by
  have heq : pivotMatrix1600 = (fun u v => node1600 (pivotPermutation1600 u) v) := by apply Matrix.ext; unfold pivotMatrix1600 node1600 pivotPermutation1600; decide +kernel
  have hmoment : injectiveMoment H node1600 = injectiveMoment H pivotMatrix1600 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1600 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1600 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1600 (0 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (0 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1600 (1 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (1 : Fin 4) = raw1717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw1717; decide +kernel
    rw [heq]
    exact (canonical1717 hH).trans (sound896 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1600 (2 : Fin 4)) =
      Sparse.eval value1166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (2 : Fin 4) = raw1714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw1714; decide +kernel
    rw [heq]
    exact (canonical1714 hH).trans (sound1166 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1600 (3 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1600 (3 : Fin 4) = raw1713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1600 raw1713; decide +kernel
    rw [heq]
    exact (canonical1713 hH).trans (sound469 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1600 + (injectiveMoment H (mergeFirst pivotMatrix1600 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1600 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1600 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1600 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1600, value1166, value1190, value469, value896, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1601 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1601 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem sound1601 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1601 = Sparse.eval value1601 (momentVector H) := by
  have heq : pivotMatrix1601 = (fun u v => node1601 (pivotPermutation1601 u) v) := by apply Matrix.ext; unfold pivotMatrix1601 node1601 pivotPermutation1601; decide +kernel
  have hmoment : injectiveMoment H node1601 = injectiveMoment H pivotMatrix1601 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1601 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1601 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1601 (0 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1601 (0 : Fin 4) = raw2107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1601 raw2107; decide +kernel
    rw [heq]
    exact (canonical2107 hH).trans (sound1016 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1601 (1 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1601 (1 : Fin 4) = raw1723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1601 raw1723; decide +kernel
    rw [heq]
    exact (canonical1723 hH).trans (sound1234 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1601 (2 : Fin 4)) =
      Sparse.eval value954 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1601 (2 : Fin 4) = raw1718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1601 raw1718; decide +kernel
    rw [heq]
    exact (canonical1718 hH).trans (sound954 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1601 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1601 (3 : Fin 4) = raw1717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1601 raw1717; decide +kernel
    rw [heq]
    exact (canonical1717 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1601 + (injectiveMoment H (mergeFirst pivotMatrix1601 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1601 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1601 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1601 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1601, value1016, value1234, value896, value954, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1602 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1602 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem sound1602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1602 = Sparse.eval value1602 (momentVector H) := by
  have heq : pivotMatrix1602 = (fun u v => node1602 (pivotPermutation1602 u) v) := by apply Matrix.ext; unfold pivotMatrix1602 node1602 pivotPermutation1602; decide +kernel
  have hmoment : injectiveMoment H node1602 = injectiveMoment H pivotMatrix1602 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1602 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1602 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1602 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1602 (0 : Fin 4) = raw2109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1602 raw2109; decide +kernel
    rw [heq]
    exact (canonical2109 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1602 (1 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1602 (1 : Fin 4) = raw1725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1602 raw1725; decide +kernel
    rw [heq]
    exact (canonical1725 hH).trans (sound466 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1602 (2 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1602 (2 : Fin 4) = raw1721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1602 raw1721; decide +kernel
    rw [heq]
    exact (canonical1721 hH).trans (sound771 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1602 (3 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1602 (3 : Fin 4) = raw1720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1602 raw1720; decide +kernel
    rw [heq]
    exact (canonical1720 hH).trans (sound460 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1602 + (injectiveMoment H (mergeFirst pivotMatrix1602 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1602 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1602 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1602 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1602, value1036, value460, value466, value771, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1603 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1603 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1603 = Sparse.eval value1603 (momentVector H) := by
  have heq : pivotMatrix1603 = (fun u v => node1603 (pivotPermutation1603 u) v) := by apply Matrix.ext; unfold pivotMatrix1603 node1603 pivotPermutation1603; decide +kernel
  have hmoment : injectiveMoment H node1603 = injectiveMoment H pivotMatrix1603 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1603 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1603 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1603 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1603 (0 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1603 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1603 (1 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1603 (1 : Fin 4) = raw1727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1603 raw1727; decide +kernel
    rw [heq]
    exact (canonical1727 hH).trans (sound1080 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1603 (2 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1603 (2 : Fin 4) = raw1723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1603 raw1723; decide +kernel
    rw [heq]
    exact (canonical1723 hH).trans (sound1234 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1603 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1603 (3 : Fin 4) = raw1722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1603 raw1722; decide +kernel
    rw [heq]
    exact (canonical1722 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1603 + (injectiveMoment H (mergeFirst pivotMatrix1603 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1603 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1603 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1603 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1603, value1079, value1080, value1234, value769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1604 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1604 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound1604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1604 = Sparse.eval value1604 (momentVector H) := by
  have heq : pivotMatrix1604 = (fun u v => node1604 (pivotPermutation1604 u) v) := by apply Matrix.ext; unfold pivotMatrix1604 node1604 pivotPermutation1604; decide +kernel
  have hmoment : injectiveMoment H node1604 = injectiveMoment H pivotMatrix1604 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1604 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1604 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1604 (0 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1604 (0 : Fin 4) = raw2112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1604 raw2112; decide +kernel
    rw [heq]
    exact (canonical2112 hH).trans (sound797 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1604 (1 : Fin 4)) =
      Sparse.eval value1077 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1604 (1 : Fin 4) = raw1729 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1604 raw1729; decide +kernel
    rw [heq]
    exact (canonical1729 hH).trans (sound1077 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1604 (2 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1604 (2 : Fin 4) = raw1726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1604 raw1726; decide +kernel
    rw [heq]
    exact (canonical1726 hH).trans (sound1042 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1604 (3 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1604 (3 : Fin 4) = raw1725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1604 raw1725; decide +kernel
    rw [heq]
    exact (canonical1725 hH).trans (sound466 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1604 + (injectiveMoment H (mergeFirst pivotMatrix1604 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1604 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1604 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1604 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1604, value1042, value1077, value466, value797, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1605 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1605 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound1605 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1605 = Sparse.eval value1605 (momentVector H) := by
  have heq : pivotMatrix1605 = (fun u v => node1605 (pivotPermutation1605 u) v) := by apply Matrix.ext; unfold pivotMatrix1605 node1605 pivotPermutation1605; decide +kernel
  have hmoment : injectiveMoment H node1605 = injectiveMoment H pivotMatrix1605 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1605 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1605 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1605 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1605 (0 : Fin 4) = raw2113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1605 raw2113; decide +kernel
    rw [heq]
    exact (canonical2113 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1605 (1 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1605 (1 : Fin 4) = raw1730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1605 raw1730; decide +kernel
    rw [heq]
    exact (canonical1730 hH).trans (sound1070 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1605 (2 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1605 (2 : Fin 4) = raw1727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1605 raw1727; decide +kernel
    rw [heq]
    exact (canonical1727 hH).trans (sound1080 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1605 (3 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1605 (3 : Fin 4) = raw1726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1605 raw1726; decide +kernel
    rw [heq]
    exact (canonical1726 hH).trans (sound1042 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1605 + (injectiveMoment H (mergeFirst pivotMatrix1605 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1605 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1605 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1605 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1605, value1042, value1063, value1070, value1080, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1606 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1606 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem sound1606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1606 = Sparse.eval value1606 (momentVector H) := by
  have heq : pivotMatrix1606 = (fun u v => node1606 (pivotPermutation1606 u) v) := by apply Matrix.ext; unfold pivotMatrix1606 node1606 pivotPermutation1606; decide +kernel
  have hmoment : injectiveMoment H node1606 = injectiveMoment H pivotMatrix1606 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1606 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1606 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1606 (0 : Fin 4)) =
      Sparse.eval value1302 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1606 (0 : Fin 4) = raw2977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1606 raw2977; decide +kernel
    rw [heq]
    exact (canonical2977 hH).trans (sound1302 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1606 (1 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1606 (1 : Fin 4) = raw1695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1606 raw1695; decide +kernel
    rw [heq]
    exact (canonical1695 hH).trans (sound1113 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1606 (2 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1606 (2 : Fin 4) = raw1632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1606 raw1632; decide +kernel
    rw [heq]
    exact (canonical1632 hH).trans (sound459 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1606 (3 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1606 (3 : Fin 4) = raw1621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1606 raw1621; decide +kernel
    rw [heq]
    exact (canonical1621 hH).trans (sound775 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1606 + (injectiveMoment H (mergeFirst pivotMatrix1606 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1606 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1606 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1606 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1606, value1113, value1302, value459, value775, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1607 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1607 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound1607 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1607 = Sparse.eval value1607 (momentVector H) := by
  have heq : pivotMatrix1607 = (fun u v => node1607 (pivotPermutation1607 u) v) := by apply Matrix.ext; unfold pivotMatrix1607 node1607 pivotPermutation1607; decide +kernel
  have hmoment : injectiveMoment H node1607 = injectiveMoment H pivotMatrix1607 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1607 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1607 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1607 (0 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1607 (0 : Fin 4) = raw3157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1607 raw3157; decide +kernel
    rw [heq]
    exact (canonical3157 hH).trans (sound1056 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1607 (1 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1607 (1 : Fin 4) = raw1706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1607 raw1706; decide +kernel
    rw [heq]
    exact (canonical1706 hH).trans (sound467 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1607 (2 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1607 (2 : Fin 4) = raw1643 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1607 raw1643; decide +kernel
    rw [heq]
    exact (canonical1643 hH).trans (sound772 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1607 (3 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1607 (3 : Fin 4) = raw1640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1607 raw1640; decide +kernel
    rw [heq]
    exact (canonical1640 hH).trans (sound447 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1607 + (injectiveMoment H (mergeFirst pivotMatrix1607 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1607 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1607 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1607 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1607, value1056, value447, value467, value772, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1608 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1608 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem sound1608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1608 = Sparse.eval value1608 (momentVector H) := by
  have heq : pivotMatrix1608 = (fun u v => node1608 (pivotPermutation1608 u) v) := by apply Matrix.ext; unfold pivotMatrix1608 node1608 pivotPermutation1608; decide +kernel
  have hmoment : injectiveMoment H node1608 = injectiveMoment H pivotMatrix1608 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1608 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1608 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1608 (0 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1608 (0 : Fin 4) = raw5611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1608 raw5611; decide +kernel
    rw [heq]
    exact (canonical5611 hH).trans (sound772 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1608 (1 : Fin 4)) =
      Sparse.eval value465 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1608 (1 : Fin 4) = raw1733 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1608 raw1733; decide +kernel
    rw [heq]
    exact (canonical1733 hH).trans (sound465 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1608 (2 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1608 (2 : Fin 4) = raw1643 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1608 raw1643; decide +kernel
    rw [heq]
    exact (canonical1643 hH).trans (sound772 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1608 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1608 (3 : Fin 4) = raw1629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1608 raw1629; decide +kernel
    rw [heq]
    exact (canonical1629 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1608 + (injectiveMoment H (mergeFirst pivotMatrix1608 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1608 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1608 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1608 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1608, value465, value772, value773, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1609 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1609 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound1609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1609 = Sparse.eval value1609 (momentVector H) := by
  have heq : pivotMatrix1609 = (fun u v => node1609 (pivotPermutation1609 u) v) := by apply Matrix.ext; unfold pivotMatrix1609 node1609 pivotPermutation1609; decide +kernel
  have hmoment : injectiveMoment H node1609 = injectiveMoment H pivotMatrix1609 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1609 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1609 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1609 (0 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1609 (0 : Fin 4) = raw5612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1609 raw5612; decide +kernel
    rw [heq]
    exact (canonical5612 hH).trans (sound773 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1609 (1 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1609 (1 : Fin 4) = raw1734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1609 raw1734; decide +kernel
    rw [heq]
    exact (canonical1734 hH).trans (sound469 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1609 (2 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1609 (2 : Fin 4) = raw1644 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1609 raw1644; decide +kernel
    rw [heq]
    exact (canonical1644 hH).trans (sound772 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1609 (3 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1609 (3 : Fin 4) = raw1632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1609 raw1632; decide +kernel
    rw [heq]
    exact (canonical1632 hH).trans (sound459 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1609 + (injectiveMoment H (mergeFirst pivotMatrix1609 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1609 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1609 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1609 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1609, value459, value469, value772, value773, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1610 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1610 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem sound1610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1610 = Sparse.eval value1610 (momentVector H) := by
  have heq : pivotMatrix1610 = (fun u v => node1610 (pivotPermutation1610 u) v) := by apply Matrix.ext; unfold pivotMatrix1610 node1610 pivotPermutation1610; decide +kernel
  have hmoment : injectiveMoment H node1610 = injectiveMoment H pivotMatrix1610 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1610 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1610 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1610 (0 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (0 : Fin 4) = raw6289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw6289; decide +kernel
    rw [heq]
    exact (canonical6289 hH).trans (sound975 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1610 (1 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (1 : Fin 4) = raw1739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw1739; decide +kernel
    rw [heq]
    exact (canonical1739 hH).trans (sound468 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1610 (2 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (2 : Fin 4) = raw1646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw1646; decide +kernel
    rw [heq]
    exact (canonical1646 hH).trans (sound447 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1610 (3 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1610 (3 : Fin 4) = raw1632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1610 raw1632; decide +kernel
    rw [heq]
    exact (canonical1632 hH).trans (sound459 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1610 + (injectiveMoment H (mergeFirst pivotMatrix1610 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1610 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1610 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1610 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1610, value447, value459, value468, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1611 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1611 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem sound1611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1611 = Sparse.eval value1611 (momentVector H) := by
  have heq : pivotMatrix1611 = (fun u v => node1611 (pivotPermutation1611 u) v) := by apply Matrix.ext; unfold pivotMatrix1611 node1611 pivotPermutation1611; decide +kernel
  have hmoment : injectiveMoment H node1611 = injectiveMoment H pivotMatrix1611 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1611 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1611 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1611 (0 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1611 (0 : Fin 4) = raw6089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1611 raw6089; decide +kernel
    rw [heq]
    exact (canonical6089 hH).trans (sound917 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1611 (1 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1611 (1 : Fin 4) = raw1738 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1611 raw1738; decide +kernel
    rw [heq]
    exact (canonical1738 hH).trans (sound454 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1611 (2 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1611 (2 : Fin 4) = raw1646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1611 raw1646; decide +kernel
    rw [heq]
    exact (canonical1646 hH).trans (sound447 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1611 (3 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1611 (3 : Fin 4) = raw1634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1611 raw1634; decide +kernel
    rw [heq]
    exact (canonical1634 hH).trans (sound450 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1611 + (injectiveMoment H (mergeFirst pivotMatrix1611 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1611 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1611 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1611 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1611, value447, value450, value454, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1612 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1612 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem sound1612 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1612 = Sparse.eval value1612 (momentVector H) := by
  have heq : pivotMatrix1612 = (fun u v => node1612 (pivotPermutation1612 u) v) := by apply Matrix.ext; unfold pivotMatrix1612 node1612 pivotPermutation1612; decide +kernel
  have hmoment : injectiveMoment H node1612 = injectiveMoment H pivotMatrix1612 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1612 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1612 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1612 (0 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1612 (0 : Fin 4) = raw6291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1612 raw6291; decide +kernel
    rw [heq]
    exact (canonical6291 hH).trans (sound976 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1612 (1 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1612 (1 : Fin 4) = raw1740 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1612 raw1740; decide +kernel
    rw [heq]
    exact (canonical1740 hH).trans (sound460 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1612 (2 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1612 (2 : Fin 4) = raw1647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1612 raw1647; decide +kernel
    rw [heq]
    exact (canonical1647 hH).trans (sound460 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1612 (3 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1612 (3 : Fin 4) = raw1637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1612 raw1637; decide +kernel
    rw [heq]
    exact (canonical1637 hH).trans (sound396 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1612 + (injectiveMoment H (mergeFirst pivotMatrix1612 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1612 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1612 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1612 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1612, value396, value460, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1613 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1613 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound1613 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1613 = Sparse.eval value1613 (momentVector H) := by
  have heq : pivotMatrix1613 = (fun u v => node1613 (pivotPermutation1613 u) v) := by apply Matrix.ext; unfold pivotMatrix1613 node1613 pivotPermutation1613; decide +kernel
  have hmoment : injectiveMoment H node1613 = injectiveMoment H pivotMatrix1613 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1613 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1613 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1613 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1613 (0 : Fin 4) = raw5614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1613 raw5614; decide +kernel
    rw [heq]
    exact (canonical5614 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1613 (1 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1613 (1 : Fin 4) = raw1736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1613 raw1736; decide +kernel
    rw [heq]
    exact (canonical1736 hH).trans (sound1234 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1613 (2 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1613 (2 : Fin 4) = raw1645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1613 raw1645; decide +kernel
    rw [heq]
    exact (canonical1645 hH).trans (sound771 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1613 (3 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1613 (3 : Fin 4) = raw1637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1613 raw1637; decide +kernel
    rw [heq]
    exact (canonical1637 hH).trans (sound396 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1613 + (injectiveMoment H (mergeFirst pivotMatrix1613 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1613 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1613 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1613 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1613, value1234, value396, value771, value775, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1614 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1614 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound1614 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1614 = Sparse.eval value1614 (momentVector H) := by
  have heq : pivotMatrix1614 = (fun u v => node1614 (pivotPermutation1614 u) v) := by apply Matrix.ext; unfold pivotMatrix1614 node1614 pivotPermutation1614; decide +kernel
  have hmoment : injectiveMoment H node1614 = injectiveMoment H pivotMatrix1614 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1614 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1614 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1614 (0 : Fin 4)) =
      Sparse.eval value1227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1614 (0 : Fin 4) = raw3005 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1614 raw3005; decide +kernel
    rw [heq]
    exact (canonical3005 hH).trans (sound1227 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1614 (1 : Fin 4)) =
      Sparse.eval value1273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1614 (1 : Fin 4) = raw1711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1614 raw1711; decide +kernel
    rw [heq]
    exact (canonical1711 hH).trans (sound1273 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1614 (2 : Fin 4)) =
      Sparse.eval value981 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1614 (2 : Fin 4) = raw1667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1614 raw1667; decide +kernel
    rw [heq]
    exact (canonical1667 hH).trans (sound981 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1614 (3 : Fin 4)) =
      Sparse.eval value1272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1614 (3 : Fin 4) = raw1664 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1614 raw1664; decide +kernel
    rw [heq]
    exact (canonical1664 hH).trans (sound1272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1614 + (injectiveMoment H (mergeFirst pivotMatrix1614 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1614 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1614 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1614 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1614, value1227, value1272, value1273, value981, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1615 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1615 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem sound1615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1615 = Sparse.eval value1615 (momentVector H) := by
  have heq : pivotMatrix1615 = (fun u v => node1615 (pivotPermutation1615 u) v) := by apply Matrix.ext; unfold pivotMatrix1615 node1615 pivotPermutation1615; decide +kernel
  have hmoment : injectiveMoment H node1615 = injectiveMoment H pivotMatrix1615 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1615 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1615 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1615 (0 : Fin 4)) =
      Sparse.eval value1298 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1615 (0 : Fin 4) = raw3006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1615 raw3006; decide +kernel
    rw [heq]
    exact (canonical3006 hH).trans (sound1298 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1615 (1 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1615 (1 : Fin 4) = raw1712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1615 raw1712; decide +kernel
    rw [heq]
    exact (canonical1712 hH).trans (sound468 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1615 (2 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1615 (2 : Fin 4) = raw1668 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1615 raw1668; decide +kernel
    rw [heq]
    exact (canonical1668 hH).trans (sound1170 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1615 (3 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1615 (3 : Fin 4) = raw1665 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1615 raw1665; decide +kernel
    rw [heq]
    exact (canonical1665 hH).trans (sound1341 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1615 + (injectiveMoment H (mergeFirst pivotMatrix1615 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1615 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1615 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1615 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1615, value1170, value1298, value1341, value468, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1616 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1616 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1616 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1616 = Sparse.eval value1616 (momentVector H) := by
  have heq : pivotMatrix1616 = (fun u v => node1616 (pivotPermutation1616 u) v) := by apply Matrix.ext; unfold pivotMatrix1616 node1616 pivotPermutation1616; decide +kernel
  have hmoment : injectiveMoment H node1616 = injectiveMoment H pivotMatrix1616 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1616 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1616 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1616 (0 : Fin 4)) =
      Sparse.eval value1082 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1616 (0 : Fin 4) = raw3029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1616 raw3029; decide +kernel
    rw [heq]
    exact (canonical3029 hH).trans (sound1082 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1616 (1 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1616 (1 : Fin 4) = raw1727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1616 raw1727; decide +kernel
    rw [heq]
    exact (canonical1727 hH).trans (sound1080 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1616 (2 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1616 (2 : Fin 4) = raw1708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1616 raw1708; decide +kernel
    rw [heq]
    exact (canonical1708 hH).trans (sound1042 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1616 (3 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1616 (3 : Fin 4) = raw1706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1616 raw1706; decide +kernel
    rw [heq]
    exact (canonical1706 hH).trans (sound467 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1616 + (injectiveMoment H (mergeFirst pivotMatrix1616 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1616 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1616 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1616 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1616, value1042, value1080, value1082, value467, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1617 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1617 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound1617 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1617 = Sparse.eval value1617 (momentVector H) := by
  have heq : pivotMatrix1617 = (fun u v => node1617 (pivotPermutation1617 u) v) := by apply Matrix.ext; unfold pivotMatrix1617 node1617 pivotPermutation1617; decide +kernel
  have hmoment : injectiveMoment H node1617 = injectiveMoment H pivotMatrix1617 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1617 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1617 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1617 (0 : Fin 4)) =
      Sparse.eval value1069 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1617 (0 : Fin 4) = raw3031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1617 raw3031; decide +kernel
    rw [heq]
    exact (canonical3031 hH).trans (sound1069 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1617 (1 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1617 (1 : Fin 4) = raw1730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1617 raw1730; decide +kernel
    rw [heq]
    exact (canonical1730 hH).trans (sound1070 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1617 (2 : Fin 4)) =
      Sparse.eval value961 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1617 (2 : Fin 4) = raw1710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1617 raw1710; decide +kernel
    rw [heq]
    exact (canonical1710 hH).trans (sound961 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1617 (3 : Fin 4)) =
      Sparse.eval value1071 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1617 (3 : Fin 4) = raw1709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1617 raw1709; decide +kernel
    rw [heq]
    exact (canonical1709 hH).trans (sound1071 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1617 + (injectiveMoment H (mergeFirst pivotMatrix1617 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1617 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1617 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1617 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1617, value1069, value1070, value1071, value961, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1618 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1618 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound1618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1618 = Sparse.eval value1618 (momentVector H) := by
  have heq : pivotMatrix1618 = (fun u v => node1618 (pivotPermutation1618 u) v) := by apply Matrix.ext; unfold pivotMatrix1618 node1618 pivotPermutation1618; decide +kernel
  have hmoment : injectiveMoment H node1618 = injectiveMoment H pivotMatrix1618 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1618 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1618 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1618 (0 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1618 (0 : Fin 4) = raw5630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1618 raw5630; decide +kernel
    rw [heq]
    exact (canonical5630 hH).trans (sound787 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1618 (1 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1618 (1 : Fin 4) = raw1737 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1618 raw1737; decide +kernel
    rw [heq]
    exact (canonical1737 hH).trans (sound786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1618 (2 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1618 (2 : Fin 4) = raw1703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1618 raw1703; decide +kernel
    rw [heq]
    exact (canonical1703 hH).trans (sound786 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1618 (3 : Fin 4)) =
      Sparse.eval value398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1618 (3 : Fin 4) = raw1697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1618 raw1697; decide +kernel
    rw [heq]
    exact (canonical1697 hH).trans (sound398 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1618 + (injectiveMoment H (mergeFirst pivotMatrix1618 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1618 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1618 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1618 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1618, value398, value786, value787, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1619 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1619 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem sound1619 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1619 = Sparse.eval value1619 (momentVector H) := by
  have heq : pivotMatrix1619 = (fun u v => node1619 (pivotPermutation1619 u) v) := by apply Matrix.ext; unfold pivotMatrix1619 node1619 pivotPermutation1619; decide +kernel
  have hmoment : injectiveMoment H node1619 = injectiveMoment H pivotMatrix1619 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1619 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1619 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1619 (0 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1619 (0 : Fin 4) = raw2163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1619 raw2163; decide +kernel
    rw [heq]
    exact (canonical2163 hH).trans (sound497 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1619 (1 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1619 (1 : Fin 4) = raw1756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1619 raw1756; decide +kernel
    rw [heq]
    exact (canonical1756 hH).trans (sound1083 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1619 (2 : Fin 4)) =
      Sparse.eval value470 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1619 (2 : Fin 4) = raw1749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1619 raw1749; decide +kernel
    rw [heq]
    exact (canonical1749 hH).trans (sound470 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1619 (3 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1619 (3 : Fin 4) = raw1747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1619 raw1747; decide +kernel
    rw [heq]
    exact (canonical1747 hH).trans (sound991 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1619 + (injectiveMoment H (mergeFirst pivotMatrix1619 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1619 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1619 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1619 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1619, value1083, value470, value497, value991, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1620 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1620 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

theorem sound1620 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1620 = Sparse.eval value1620 (momentVector H) := by
  have heq : pivotMatrix1620 = (fun u v => node1620 (pivotPermutation1620 u) v) := by apply Matrix.ext; unfold pivotMatrix1620 node1620 pivotPermutation1620; decide +kernel
  have hmoment : injectiveMoment H node1620 = injectiveMoment H pivotMatrix1620 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1620 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1620 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1620 (0 : Fin 4)) =
      Sparse.eval value794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1620 (0 : Fin 4) = raw3062 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1620 raw3062; decide +kernel
    rw [heq]
    exact (canonical3062 hH).trans (sound794 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1620 (1 : Fin 4)) =
      Sparse.eval value789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1620 (1 : Fin 4) = raw1804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1620 raw1804; decide +kernel
    rw [heq]
    exact (canonical1804 hH).trans (sound789 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1620 (2 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1620 (2 : Fin 4) = raw1747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1620 raw1747; decide +kernel
    rw [heq]
    exact (canonical1747 hH).trans (sound991 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1620 (3 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1620 (3 : Fin 4) = raw1745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1620 raw1745; decide +kernel
    rw [heq]
    exact (canonical1745 hH).trans (sound405 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1620 + (injectiveMoment H (mergeFirst pivotMatrix1620 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1620 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1620 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1620 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1620, value405, value789, value794, value991, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1621 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1621 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem sound1621 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1621 = Sparse.eval value1621 (momentVector H) := by
  have heq : pivotMatrix1621 = (fun u v => node1621 (pivotPermutation1621 u) v) := by apply Matrix.ext; unfold pivotMatrix1621 node1621 pivotPermutation1621; decide +kernel
  have hmoment : injectiveMoment H node1621 = injectiveMoment H pivotMatrix1621 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1621 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1621 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1621 (0 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1621 (0 : Fin 4) = raw3063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1621 raw3063; decide +kernel
    rw [heq]
    exact (canonical3063 hH).trans (sound791 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1621 (1 : Fin 4)) =
      Sparse.eval value793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1621 (1 : Fin 4) = raw1811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1621 raw1811; decide +kernel
    rw [heq]
    exact (canonical1811 hH).trans (sound793 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1621 (2 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1621 (2 : Fin 4) = raw1750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1621 raw1750; decide +kernel
    rw [heq]
    exact (canonical1750 hH).trans (sound791 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1621 (3 : Fin 4)) =
      Sparse.eval value470 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1621 (3 : Fin 4) = raw1749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1621 raw1749; decide +kernel
    rw [heq]
    exact (canonical1749 hH).trans (sound470 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1621 + (injectiveMoment H (mergeFirst pivotMatrix1621 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1621 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1621 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1621 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1621, value470, value791, value793, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1622 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1622 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem sound1622 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1622 = Sparse.eval value1622 (momentVector H) := by
  have heq : pivotMatrix1622 = (fun u v => node1622 (pivotPermutation1622 u) v) := by apply Matrix.ext; unfold pivotMatrix1622 node1622 pivotPermutation1622; decide +kernel
  have hmoment : injectiveMoment H node1622 = injectiveMoment H pivotMatrix1622 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1622 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1622 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1622 (0 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1622 (0 : Fin 4) = raw6391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1622 raw6391; decide +kernel
    rw [heq]
    exact (canonical6391 hH).trans (sound995 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1622 (1 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1622 (1 : Fin 4) = raw2119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1622 raw2119; decide +kernel
    rw [heq]
    exact (canonical2119 hH).trans (sound491 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1622 (2 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1622 (2 : Fin 4) = raw1751 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1622 raw1751; decide +kernel
    rw [heq]
    exact (canonical1751 hH).trans (sound466 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1622 (3 : Fin 4)) =
      Sparse.eval value470 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1622 (3 : Fin 4) = raw1749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1622 raw1749; decide +kernel
    rw [heq]
    exact (canonical1749 hH).trans (sound470 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1622 + (injectiveMoment H (mergeFirst pivotMatrix1622 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1622 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1622 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1622 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1622, value466, value470, value491, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1623 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1623 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

theorem sound1623 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1623 = Sparse.eval value1623 (momentVector H) := by
  have heq : pivotMatrix1623 = (fun u v => node1623 (pivotPermutation1623 u) v) := by apply Matrix.ext; unfold pivotMatrix1623 node1623 pivotPermutation1623; decide +kernel
  have hmoment : injectiveMoment H node1623 = injectiveMoment H pivotMatrix1623 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1623 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1623 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1623 (0 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1623 (0 : Fin 4) = raw1126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1623 raw1126; decide +kernel
    rw [heq]
    exact (canonical1126 hH).trans (sound1155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1623 (1 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1623 (1 : Fin 4) = raw1849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1623 raw1849; decide +kernel
    rw [heq]
    exact (canonical1849 hH).trans (sound799 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1623 (2 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1623 (2 : Fin 4) = raw2012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1623 raw2012; decide +kernel
    rw [heq]
    exact (canonical2012 hH).trans (sound807 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1623 (3 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1623 (3 : Fin 4) = raw2038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1623 raw2038; decide +kernel
    rw [heq]
    exact (canonical2038 hH).trans (sound1066 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1623 + (injectiveMoment H (mergeFirst pivotMatrix1623 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1623 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1623 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1623 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1623, value1066, value1155, value799, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1624 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1624 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem sound1624 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1624 = Sparse.eval value1624 (momentVector H) := by
  have heq : pivotMatrix1624 = (fun u v => node1624 (pivotPermutation1624 u) v) := by apply Matrix.ext; unfold pivotMatrix1624 node1624 pivotPermutation1624; decide +kernel
  have hmoment : injectiveMoment H node1624 = injectiveMoment H pivotMatrix1624 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1624 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1624 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1624 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1624 (0 : Fin 4) = raw1131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1624 raw1131; decide +kernel
    rw [heq]
    exact (canonical1131 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1624 (1 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1624 (1 : Fin 4) = raw1860 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1624 raw1860; decide +kernel
    rw [heq]
    exact (canonical1860 hH).trans (sound797 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1624 (2 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1624 (2 : Fin 4) = raw2045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1624 raw2045; decide +kernel
    rw [heq]
    exact (canonical2045 hH).trans (sound1013 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1624 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1624 (3 : Fin 4) = raw2051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1624 raw2051; decide +kernel
    rw [heq]
    exact (canonical2051 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1624 + (injectiveMoment H (mergeFirst pivotMatrix1624 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1624 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1624 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1624 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1624, value1013, value1063, value797, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1625 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1625 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound1625 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1625 = Sparse.eval value1625 (momentVector H) := by
  have heq : pivotMatrix1625 = (fun u v => node1625 (pivotPermutation1625 u) v) := by apply Matrix.ext; unfold pivotMatrix1625 node1625 pivotPermutation1625; decide +kernel
  have hmoment : injectiveMoment H node1625 = injectiveMoment H pivotMatrix1625 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1625 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1625 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1625 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1625 (0 : Fin 4) = raw1157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1625 raw1157; decide +kernel
    rw [heq]
    exact (canonical1157 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1625 (1 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1625 (1 : Fin 4) = raw1978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1625 raw1978; decide +kernel
    rw [heq]
    exact (canonical1978 hH).trans (sound805 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1625 (2 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1625 (2 : Fin 4) = raw2087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1625 raw2087; decide +kernel
    rw [heq]
    exact (canonical2087 hH).trans (sound491 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1625 (3 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1625 (3 : Fin 4) = raw2090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1625 raw2090; decide +kernel
    rw [heq]
    exact (canonical2090 hH).trans (sound1041 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1625 + (injectiveMoment H (mergeFirst pivotMatrix1625 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1625 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1625 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1625 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1625, value1041, value491, value805, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1626 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1626 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem sound1626 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1626 = Sparse.eval value1626 (momentVector H) := by
  have heq : pivotMatrix1626 = (fun u v => node1626 (pivotPermutation1626 u) v) := by apply Matrix.ext; unfold pivotMatrix1626 node1626 pivotPermutation1626; decide +kernel
  have hmoment : injectiveMoment H node1626 = injectiveMoment H pivotMatrix1626 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1626 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1626 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1626 (0 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1626 (0 : Fin 4) = raw1162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1626 raw1162; decide +kernel
    rw [heq]
    exact (canonical1162 hH).trans (sound1155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1626 (1 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1626 (1 : Fin 4) = raw2048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1626 raw2048; decide +kernel
    rw [heq]
    exact (canonical2048 hH).trans (sound1063 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1626 (2 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1626 (2 : Fin 4) = raw2104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1626 raw2104; decide +kernel
    rw [heq]
    exact (canonical2104 hH).trans (sound495 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1626 (3 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1626 (3 : Fin 4) = raw2108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1626 raw2108; decide +kernel
    rw [heq]
    exact (canonical2108 hH).trans (sound1016 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1626 + (injectiveMoment H (mergeFirst pivotMatrix1626 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1626 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1626 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1626 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1626, value1016, value1063, value1155, value495, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1627 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1627 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem sound1627 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1627 = Sparse.eval value1627 (momentVector H) := by
  have heq : pivotMatrix1627 = (fun u v => node1627 (pivotPermutation1627 u) v) := by apply Matrix.ext; unfold pivotMatrix1627 node1627 pivotPermutation1627; decide +kernel
  have hmoment : injectiveMoment H node1627 = injectiveMoment H pivotMatrix1627 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1627 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1627 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1627 (0 : Fin 4)) =
      Sparse.eval value1351 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1627 (0 : Fin 4) = raw1191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1627 raw1191; decide +kernel
    rw [heq]
    exact (canonical1191 hH).trans (sound1351 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1627 (1 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1627 (1 : Fin 4) = raw1756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1627 raw1756; decide +kernel
    rw [heq]
    exact (canonical1756 hH).trans (sound1083 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1627 (2 : Fin 4)) =
      Sparse.eval value796 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1627 (2 : Fin 4) = raw1836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1627 raw1836; decide +kernel
    rw [heq]
    exact (canonical1836 hH).trans (sound796 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1627 (3 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1627 (3 : Fin 4) = raw1845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1627 raw1845; decide +kernel
    rw [heq]
    exact (canonical1845 hH).trans (sound1032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1627 + (injectiveMoment H (mergeFirst pivotMatrix1627 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1627 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1627 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1627 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1627, value1032, value1083, value1351, value796, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1628 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1628 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

theorem sound1628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1628 = Sparse.eval value1628 (momentVector H) := by
  have heq : pivotMatrix1628 = (fun u v => node1628 (pivotPermutation1628 u) v) := by apply Matrix.ext; unfold pivotMatrix1628 node1628 pivotPermutation1628; decide +kernel
  have hmoment : injectiveMoment H node1628 = injectiveMoment H pivotMatrix1628 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1628 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1628 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1628 (0 : Fin 4)) =
      Sparse.eval value1120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1628 (0 : Fin 4) = raw1197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1628 raw1197; decide +kernel
    rw [heq]
    exact (canonical1197 hH).trans (sound1120 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1628 (1 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1628 (1 : Fin 4) = raw1758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1628 raw1758; decide +kernel
    rw [heq]
    exact (canonical1758 hH).trans (sound819 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1628 (2 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1628 (2 : Fin 4) = raw1849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1628 raw1849; decide +kernel
    rw [heq]
    exact (canonical1849 hH).trans (sound799 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1628 (3 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1628 (3 : Fin 4) = raw1856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1628 raw1856; decide +kernel
    rw [heq]
    exact (canonical1856 hH).trans (sound816 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1628 + (injectiveMoment H (mergeFirst pivotMatrix1628 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1628 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1628 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1628 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1628, value1120, value799, value816, value819, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1629 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1629 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem sound1629 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1629 = Sparse.eval value1629 (momentVector H) := by
  have heq : pivotMatrix1629 = (fun u v => node1629 (pivotPermutation1629 u) v) := by apply Matrix.ext; unfold pivotMatrix1629 node1629 pivotPermutation1629; decide +kernel
  have hmoment : injectiveMoment H node1629 = injectiveMoment H pivotMatrix1629 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1629 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1629 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1629 (0 : Fin 4)) =
      Sparse.eval value1329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1629 (0 : Fin 4) = raw1206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1629 raw1206; decide +kernel
    rw [heq]
    exact (canonical1206 hH).trans (sound1329 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1629 (1 : Fin 4)) =
      Sparse.eval value471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1629 (1 : Fin 4) = raw1771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1629 raw1771; decide +kernel
    rw [heq]
    exact (canonical1771 hH).trans (sound471 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1629 (2 : Fin 4)) =
      Sparse.eval value1197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1629 (2 : Fin 4) = raw1873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1629 raw1873; decide +kernel
    rw [heq]
    exact (canonical1873 hH).trans (sound1197 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1629 (3 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1629 (3 : Fin 4) = raw1893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1629 raw1893; decide +kernel
    rw [heq]
    exact (canonical1893 hH).trans (sound803 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1629 + (injectiveMoment H (mergeFirst pivotMatrix1629 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1629 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1629 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1629 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1629, value1197, value1329, value471, value803, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1630 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1630 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem sound1630 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1630 = Sparse.eval value1630 (momentVector H) := by
  have heq : pivotMatrix1630 = (fun u v => node1630 (pivotPermutation1630 u) v) := by apply Matrix.ext; unfold pivotMatrix1630 node1630 pivotPermutation1630; decide +kernel
  have hmoment : injectiveMoment H node1630 = injectiveMoment H pivotMatrix1630 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1630 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1630 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1630 (0 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1630 (0 : Fin 4) = raw1211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1630 raw1211; decide +kernel
    rw [heq]
    exact (canonical1211 hH).trans (sound1222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1630 (1 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1630 (1 : Fin 4) = raw1777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1630 raw1777; decide +kernel
    rw [heq]
    exact (canonical1777 hH).trans (sound1347 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1630 (2 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1630 (2 : Fin 4) = raw1877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1630 raw1877; decide +kernel
    rw [heq]
    exact (canonical1877 hH).trans (sound272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1630 (3 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1630 (3 : Fin 4) = raw1902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1630 raw1902; decide +kernel
    rw [heq]
    exact (canonical1902 hH).trans (sound1221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1630 + (injectiveMoment H (mergeFirst pivotMatrix1630 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1630 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1630 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1630 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1630, value1221, value1222, value1347, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1631 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1631 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem sound1631 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1631 = Sparse.eval value1631 (momentVector H) := by
  have heq : pivotMatrix1631 = (fun u v => node1631 (pivotPermutation1631 u) v) := by apply Matrix.ext; unfold pivotMatrix1631 node1631 pivotPermutation1631; decide +kernel
  have hmoment : injectiveMoment H node1631 = injectiveMoment H pivotMatrix1631 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1631 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1631 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1631 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1631 (0 : Fin 4) = raw1216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1631 raw1216; decide +kernel
    rw [heq]
    exact (canonical1216 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1631 (1 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1631 (1 : Fin 4) = raw1784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1631 raw1784; decide +kernel
    rw [heq]
    exact (canonical1784 hH).trans (sound975 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1631 (2 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1631 (2 : Fin 4) = raw1887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1631 raw1887; decide +kernel
    rw [heq]
    exact (canonical1887 hH).trans (sound967 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1631 (3 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1631 (3 : Fin 4) = raw1912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1631 raw1912; decide +kernel
    rw [heq]
    exact (canonical1912 hH).trans (sound974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1631 + (injectiveMoment H (mergeFirst pivotMatrix1631 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1631 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1631 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1631 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1631, value967, value973, value974, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1632 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1632 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem sound1632 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1632 = Sparse.eval value1632 (momentVector H) := by
  have heq : pivotMatrix1632 = (fun u v => node1632 (pivotPermutation1632 u) v) := by apply Matrix.ext; unfold pivotMatrix1632 node1632 pivotPermutation1632; decide +kernel
  have hmoment : injectiveMoment H node1632 = injectiveMoment H pivotMatrix1632 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1632 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1632 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1632 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1632 (0 : Fin 4) = raw1218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1632 raw1218; decide +kernel
    rw [heq]
    exact (canonical1218 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1632 (1 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1632 (1 : Fin 4) = raw1786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1632 raw1786; decide +kernel
    rw [heq]
    exact (canonical1786 hH).trans (sound472 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1632 (2 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1632 (2 : Fin 4) = raw1902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1632 raw1902; decide +kernel
    rw [heq]
    exact (canonical1902 hH).trans (sound1221 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1632 (3 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1632 (3 : Fin 4) = raw1919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1632 raw1919; decide +kernel
    rw [heq]
    exact (canonical1919 hH).trans (sound1223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1632 + (injectiveMoment H (mergeFirst pivotMatrix1632 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1632 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1632 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1632 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1632, value1221, value1223, value472, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1633 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1633 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem sound1633 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1633 = Sparse.eval value1633 (momentVector H) := by
  have heq : pivotMatrix1633 = (fun u v => node1633 (pivotPermutation1633 u) v) := by apply Matrix.ext; unfold pivotMatrix1633 node1633 pivotPermutation1633; decide +kernel
  have hmoment : injectiveMoment H node1633 = injectiveMoment H pivotMatrix1633 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1633 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1633 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1633 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1633 (0 : Fin 4) = raw1222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1633 raw1222; decide +kernel
    rw [heq]
    exact (canonical1222 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1633 (1 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1633 (1 : Fin 4) = raw1791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1633 raw1791; decide +kernel
    rw [heq]
    exact (canonical1791 hH).trans (sound474 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1633 (2 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1633 (2 : Fin 4) = raw1916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1633 raw1916; decide +kernel
    rw [heq]
    exact (canonical1916 hH).trans (sound802 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1633 (3 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1633 (3 : Fin 4) = raw1929 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1633 raw1929; decide +kernel
    rw [heq]
    exact (canonical1929 hH).trans (sound807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1633 + (injectiveMoment H (mergeFirst pivotMatrix1633 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1633 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1633 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1633 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1633, value474, value802, value807, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1634 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1634 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem sound1634 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1634 = Sparse.eval value1634 (momentVector H) := by
  have heq : pivotMatrix1634 = (fun u v => node1634 (pivotPermutation1634 u) v) := by apply Matrix.ext; unfold pivotMatrix1634 node1634 pivotPermutation1634; decide +kernel
  have hmoment : injectiveMoment H node1634 = injectiveMoment H pivotMatrix1634 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1634 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1634 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1634 (0 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1634 (0 : Fin 4) = raw1223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1634 raw1223; decide +kernel
    rw [heq]
    exact (canonical1223 hH).trans (sound1222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1634 (1 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1634 (1 : Fin 4) = raw1793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1634 raw1793; decide +kernel
    rw [heq]
    exact (canonical1793 hH).trans (sound1277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1634 (2 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1634 (2 : Fin 4) = raw1934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1634 raw1934; decide +kernel
    rw [heq]
    exact (canonical1934 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1634 (3 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1634 (3 : Fin 4) = raw1936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1634 raw1936; decide +kernel
    rw [heq]
    exact (canonical1936 hH).trans (sound1202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1634 + (injectiveMoment H (mergeFirst pivotMatrix1634 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1634 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1634 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1634 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1634, value1202, value1207, value1222, value1277, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1635 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1635 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem sound1635 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1635 = Sparse.eval value1635 (momentVector H) := by
  have heq : pivotMatrix1635 = (fun u v => node1635 (pivotPermutation1635 u) v) := by apply Matrix.ext; unfold pivotMatrix1635 node1635 pivotPermutation1635; decide +kernel
  have hmoment : injectiveMoment H node1635 = injectiveMoment H pivotMatrix1635 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1635 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1635 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1635 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1635 (0 : Fin 4) = raw1224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1635 raw1224; decide +kernel
    rw [heq]
    exact (canonical1224 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1635 (1 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1635 (1 : Fin 4) = raw1794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1635 raw1794; decide +kernel
    rw [heq]
    exact (canonical1794 hH).trans (sound944 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1635 (2 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1635 (2 : Fin 4) = raw1935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1635 raw1935; decide +kernel
    rw [heq]
    exact (canonical1935 hH).trans (sound943 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1635 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1635 (3 : Fin 4) = raw1937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1635 raw1937; decide +kernel
    rw [heq]
    exact (canonical1937 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1635 + (injectiveMoment H (mergeFirst pivotMatrix1635 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1635 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1635 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1635 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1635, value943, value944, value969, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1636 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1636 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem sound1636 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1636 = Sparse.eval value1636 (momentVector H) := by
  have heq : pivotMatrix1636 = (fun u v => node1636 (pivotPermutation1636 u) v) := by apply Matrix.ext; unfold pivotMatrix1636 node1636 pivotPermutation1636; decide +kernel
  have hmoment : injectiveMoment H node1636 = injectiveMoment H pivotMatrix1636 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1636 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1636 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1636 (0 : Fin 4)) =
      Sparse.eval value820 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1636 (0 : Fin 4) = raw1225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1636 raw1225; decide +kernel
    rw [heq]
    exact (canonical1225 hH).trans (sound820 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1636 (1 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1636 (1 : Fin 4) = raw1795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1636 raw1795; decide +kernel
    rw [heq]
    exact (canonical1795 hH).trans (sound476 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1636 (2 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1636 (2 : Fin 4) = raw1936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1636 raw1936; decide +kernel
    rw [heq]
    exact (canonical1936 hH).trans (sound1202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1636 (3 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1636 (3 : Fin 4) = raw1939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1636 raw1939; decide +kernel
    rw [heq]
    exact (canonical1939 hH).trans (sound801 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1636 + (injectiveMoment H (mergeFirst pivotMatrix1636 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1636 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1636 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1636 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1636, value1202, value476, value801, value820, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1637 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1637 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound1637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1637 = Sparse.eval value1637 (momentVector H) := by
  have heq : pivotMatrix1637 = (fun u v => node1637 (pivotPermutation1637 u) v) := by apply Matrix.ext; unfold pivotMatrix1637 node1637 pivotPermutation1637; decide +kernel
  have hmoment : injectiveMoment H node1637 = injectiveMoment H pivotMatrix1637 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1637 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1637 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1637 (0 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1637 (0 : Fin 4) = raw1250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1637 raw1250; decide +kernel
    rw [heq]
    exact (canonical1250 hH).trans (sound1104 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1637 (1 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1637 (1 : Fin 4) = raw1869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1637 raw1869; decide +kernel
    rw [heq]
    exact (canonical1869 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1637 (2 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1637 (2 : Fin 4) = raw2043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1637 raw2043; decide +kernel
    rw [heq]
    exact (canonical2043 hH).trans (sound1268 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1637 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1637 (3 : Fin 4) = raw2048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1637 raw2048; decide +kernel
    rw [heq]
    exact (canonical2048 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1637 + (injectiveMoment H (mergeFirst pivotMatrix1637 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1637 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1637 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1637 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1637, value1063, value1104, value1268, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1638 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1638 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem sound1638 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1638 = Sparse.eval value1638 (momentVector H) := by
  have heq : pivotMatrix1638 = (fun u v => node1638 (pivotPermutation1638 u) v) := by apply Matrix.ext; unfold pivotMatrix1638 node1638 pivotPermutation1638; decide +kernel
  have hmoment : injectiveMoment H node1638 = injectiveMoment H pivotMatrix1638 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1638 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1638 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1638 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (0 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1638 (1 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (1 : Fin 4) = raw1916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw1916; decide +kernel
    rw [heq]
    exact (canonical1916 hH).trans (sound802 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1638 (2 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (2 : Fin 4) = raw2053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw2053; decide +kernel
    rw [heq]
    exact (canonical2053 hH).trans (sound806 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1638 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1638 (3 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1638 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1638 + (injectiveMoment H (mergeFirst pivotMatrix1638 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1638 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1638 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1638 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1638, value802, value804, value805, value806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1639 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1639 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem sound1639 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1639 = Sparse.eval value1639 (momentVector H) := by
  have heq : pivotMatrix1639 = (fun u v => node1639 (pivotPermutation1639 u) v) := by apply Matrix.ext; unfold pivotMatrix1639 node1639 pivotPermutation1639; decide +kernel
  have hmoment : injectiveMoment H node1639 = injectiveMoment H pivotMatrix1639 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1639 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1639 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1639 (0 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1639 (0 : Fin 4) = raw1262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1639 raw1262; decide +kernel
    rw [heq]
    exact (canonical1262 hH).trans (sound815 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1639 (1 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1639 (1 : Fin 4) = raw1938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1639 raw1938; decide +kernel
    rw [heq]
    exact (canonical1938 hH).trans (sound801 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1639 (2 : Fin 4)) =
      Sparse.eval value1098 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1639 (2 : Fin 4) = raw2070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1639 raw2070; decide +kernel
    rw [heq]
    exact (canonical2070 hH).trans (sound1098 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1639 (3 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1639 (3 : Fin 4) = raw2072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1639 raw2072; decide +kernel
    rw [heq]
    exact (canonical2072 hH).trans (sound1203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1639 + (injectiveMoment H (mergeFirst pivotMatrix1639 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1639 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1639 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1639 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1639, value1098, value1203, value801, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1640 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1640 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound1640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1640 = Sparse.eval value1640 (momentVector H) := by
  have heq : pivotMatrix1640 = (fun u v => node1640 (pivotPermutation1640 u) v) := by apply Matrix.ext; unfold pivotMatrix1640 node1640 pivotPermutation1640; decide +kernel
  have hmoment : injectiveMoment H node1640 = injectiveMoment H pivotMatrix1640 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1640 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1640 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1640 (0 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1640 (0 : Fin 4) = raw1266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1640 raw1266; decide +kernel
    rw [heq]
    exact (canonical1266 hH).trans (sound995 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1640 (1 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1640 (1 : Fin 4) = raw1978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1640 raw1978; decide +kernel
    rw [heq]
    exact (canonical1978 hH).trans (sound805 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1640 (2 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1640 (2 : Fin 4) = raw2081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1640 raw2081; decide +kernel
    rw [heq]
    exact (canonical2081 hH).trans (sound1081 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1640 (3 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1640 (3 : Fin 4) = raw2083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1640 raw2083; decide +kernel
    rw [heq]
    exact (canonical2083 hH).trans (sound1043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1640 + (injectiveMoment H (mergeFirst pivotMatrix1640 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1640 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1640 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1640 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1640, value1043, value1081, value805, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1641 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1641 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound1641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1641 = Sparse.eval value1641 (momentVector H) := by
  have heq : pivotMatrix1641 = (fun u v => node1641 (pivotPermutation1641 u) v) := by apply Matrix.ext; unfold pivotMatrix1641 node1641 pivotPermutation1641; decide +kernel
  have hmoment : injectiveMoment H node1641 = injectiveMoment H pivotMatrix1641 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1641 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1641 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1641 (0 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1641 (0 : Fin 4) = raw1267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1641 raw1267; decide +kernel
    rw [heq]
    exact (canonical1267 hH).trans (sound815 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1641 (1 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1641 (1 : Fin 4) = raw1979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1641 raw1979; decide +kernel
    rw [heq]
    exact (canonical1979 hH).trans (sound802 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1641 (2 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1641 (2 : Fin 4) = raw2082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1641 raw2082; decide +kernel
    rw [heq]
    exact (canonical2082 hH).trans (sound490 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1641 (3 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1641 (3 : Fin 4) = raw2084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1641 raw2084; decide +kernel
    rw [heq]
    exact (canonical2084 hH).trans (sound1043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1641 + (injectiveMoment H (mergeFirst pivotMatrix1641 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1641 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1641 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1641 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1641, value1043, value490, value802, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1642 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1642 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound1642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1642 = Sparse.eval value1642 (momentVector H) := by
  have heq : pivotMatrix1642 = (fun u v => node1642 (pivotPermutation1642 u) v) := by apply Matrix.ext; unfold pivotMatrix1642 node1642 pivotPermutation1642; decide +kernel
  have hmoment : injectiveMoment H node1642 = injectiveMoment H pivotMatrix1642 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1642 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1642 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1642 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (0 : Fin 4) = raw1268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw1268; decide +kernel
    rw [heq]
    exact (canonical1268 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1642 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (1 : Fin 4) = raw2049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw2049; decide +kernel
    rw [heq]
    exact (canonical2049 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1642 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (2 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1642 (3 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1642 (3 : Fin 4) = raw2103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1642 raw2103; decide +kernel
    rw [heq]
    exact (canonical2103 hH).trans (sound1190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1642 + (injectiveMoment H (mergeFirst pivotMatrix1642 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1642 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1642 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1642 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1642, value1190, value1202, value476, value804, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1643 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1643 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound1643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1643 = Sparse.eval value1643 (momentVector H) := by
  have heq : pivotMatrix1643 = (fun u v => node1643 (pivotPermutation1643 u) v) := by apply Matrix.ext; unfold pivotMatrix1643 node1643 pivotPermutation1643; decide +kernel
  have hmoment : injectiveMoment H node1643 = injectiveMoment H pivotMatrix1643 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1643 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1643 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1643 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1643 (0 : Fin 4) = raw1269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1643 raw1269; decide +kernel
    rw [heq]
    exact (canonical1269 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1643 (1 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1643 (1 : Fin 4) = raw2071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1643 raw2071; decide +kernel
    rw [heq]
    exact (canonical2071 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1643 (2 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1643 (2 : Fin 4) = raw2105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1643 raw2105; decide +kernel
    rw [heq]
    exact (canonical2105 hH).trans (sound1003 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1643 (3 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1643 (3 : Fin 4) = raw2108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1643 raw2108; decide +kernel
    rw [heq]
    exact (canonical2108 hH).trans (sound1016 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1643 + (injectiveMoment H (mergeFirst pivotMatrix1643 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1643 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1643 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1643 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1643, value1003, value1016, value1036, value1203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1644 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1644 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound1644 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1644 = Sparse.eval value1644 (momentVector H) := by
  have heq : pivotMatrix1644 = (fun u v => node1644 (pivotPermutation1644 u) v) := by apply Matrix.ext; unfold pivotMatrix1644 node1644 pivotPermutation1644; decide +kernel
  have hmoment : injectiveMoment H node1644 = injectiveMoment H pivotMatrix1644 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1644 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1644 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1644 (0 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1644 (0 : Fin 4) = raw1270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1644 raw1270; decide +kernel
    rw [heq]
    exact (canonical1270 hH).trans (sound1028 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1644 (1 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1644 (1 : Fin 4) = raw2090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1644 raw2090; decide +kernel
    rw [heq]
    exact (canonical2090 hH).trans (sound1041 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1644 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1644 (2 : Fin 4) = raw2113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1644 raw2113; decide +kernel
    rw [heq]
    exact (canonical2113 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1644 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1644 (3 : Fin 4) = raw2115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1644 raw2115; decide +kernel
    rw [heq]
    exact (canonical2115 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1644 + (injectiveMoment H (mergeFirst pivotMatrix1644 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1644 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1644 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1644 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1644, value1028, value1041, value1063, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1645 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1645 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem sound1645 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1645 = Sparse.eval value1645 (momentVector H) := by
  have heq : pivotMatrix1645 = (fun u v => node1645 (pivotPermutation1645 u) v) := by apply Matrix.ext; unfold pivotMatrix1645 node1645 pivotPermutation1645; decide +kernel
  have hmoment : injectiveMoment H node1645 = injectiveMoment H pivotMatrix1645 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1645 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1645 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1645 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1645 (0 : Fin 4) = raw6408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1645 raw6408; decide +kernel
    rw [heq]
    exact (canonical6408 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1645 (1 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1645 (1 : Fin 4) = raw2122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1645 raw2122; decide +kernel
    rw [heq]
    exact (canonical2122 hH).trans (sound488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1645 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1645 (2 : Fin 4) = raw1795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1645 raw1795; decide +kernel
    rw [heq]
    exact (canonical1795 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1645 (3 : Fin 4)) =
      Sparse.eval value471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1645 (3 : Fin 4) = raw1771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1645 raw1771; decide +kernel
    rw [heq]
    exact (canonical1771 hH).trans (sound471 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1645 + (injectiveMoment H (mergeFirst pivotMatrix1645 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1645 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1645 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1645 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1645, value1005, value471, value476, value488, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1646 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1646 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound1646 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1646 = Sparse.eval value1646 (momentVector H) := by
  have heq : pivotMatrix1646 = (fun u v => node1646 (pivotPermutation1646 u) v) := by apply Matrix.ext; unfold pivotMatrix1646 node1646 pivotPermutation1646; decide +kernel
  have hmoment : injectiveMoment H node1646 = injectiveMoment H pivotMatrix1646 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1646 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1646 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1646 (0 : Fin 4)) =
      Sparse.eval value1296 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1646 (0 : Fin 4) = raw3072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1646 raw3072; decide +kernel
    rw [heq]
    exact (canonical3072 hH).trans (sound1296 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1646 (1 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1646 (1 : Fin 4) = raw1902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1646 raw1902; decide +kernel
    rw [heq]
    exact (canonical1902 hH).trans (sound1221 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1646 (2 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1646 (2 : Fin 4) = raw1786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1646 raw1786; decide +kernel
    rw [heq]
    exact (canonical1786 hH).trans (sound472 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1646 (3 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1646 (3 : Fin 4) = raw1777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1646 raw1777; decide +kernel
    rw [heq]
    exact (canonical1777 hH).trans (sound1347 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1646 + (injectiveMoment H (mergeFirst pivotMatrix1646 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1646 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1646 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1646 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1646, value1221, value1296, value1347, value472, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1647 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1647 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1647 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1647 = Sparse.eval value1647 (momentVector H) := by
  have heq : pivotMatrix1647 = (fun u v => node1647 (pivotPermutation1647 u) v) := by apply Matrix.ext; unfold pivotMatrix1647 node1647 pivotPermutation1647; decide +kernel
  have hmoment : injectiveMoment H node1647 = injectiveMoment H pivotMatrix1647 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1647 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1647 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1647 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1647 (0 : Fin 4) = raw3074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1647 raw3074; decide +kernel
    rw [heq]
    exact (canonical3074 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1647 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1647 (1 : Fin 4) = raw1912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1647 raw1912; decide +kernel
    rw [heq]
    exact (canonical1912 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1647 (2 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1647 (2 : Fin 4) = raw1788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1647 raw1788; decide +kernel
    rw [heq]
    exact (canonical1788 hH).trans (sound473 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1647 (3 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1647 (3 : Fin 4) = raw1784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1647 raw1784; decide +kernel
    rw [heq]
    exact (canonical1784 hH).trans (sound975 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1647 + (injectiveMoment H (mergeFirst pivotMatrix1647 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1647 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1647 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1647 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1647, value473, value946, value974, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1648 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1648 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound1648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1648 = Sparse.eval value1648 (momentVector H) := by
  have heq : pivotMatrix1648 = (fun u v => node1648 (pivotPermutation1648 u) v) := by apply Matrix.ext; unfold pivotMatrix1648 node1648 pivotPermutation1648; decide +kernel
  have hmoment : injectiveMoment H node1648 = injectiveMoment H pivotMatrix1648 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1648 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1648 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1648 (0 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1648 (0 : Fin 4) = raw3081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1648 raw3081; decide +kernel
    rw [heq]
    exact (canonical3081 hH).trans (sound1003 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1648 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1648 (1 : Fin 4) = raw1936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1648 raw1936; decide +kernel
    rw [heq]
    exact (canonical1936 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1648 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1648 (2 : Fin 4) = raw1795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1648 raw1795; decide +kernel
    rw [heq]
    exact (canonical1795 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1648 (3 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1648 (3 : Fin 4) = raw1793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1648 raw1793; decide +kernel
    rw [heq]
    exact (canonical1793 hH).trans (sound1277 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1648 + (injectiveMoment H (mergeFirst pivotMatrix1648 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1648 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1648 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1648 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1648, value1003, value1202, value1277, value476, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1649 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1649 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1649 = Sparse.eval value1649 (momentVector H) := by
  have heq : pivotMatrix1649 = (fun u v => node1649 (pivotPermutation1649 u) v) := by apply Matrix.ext; unfold pivotMatrix1649 node1649 pivotPermutation1649; decide +kernel
  have hmoment : injectiveMoment H node1649 = injectiveMoment H pivotMatrix1649 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1649 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1649 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1649 (0 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1649 (0 : Fin 4) = raw3082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1649 raw3082; decide +kernel
    rw [heq]
    exact (canonical3082 hH).trans (sound939 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1649 (1 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1649 (1 : Fin 4) = raw1937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1649 raw1937; decide +kernel
    rw [heq]
    exact (canonical1937 hH).trans (sound969 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1649 (2 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1649 (2 : Fin 4) = raw1796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1649 raw1796; decide +kernel
    rw [heq]
    exact (canonical1796 hH).trans (sound477 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1649 (3 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1649 (3 : Fin 4) = raw1794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1649 raw1794; decide +kernel
    rw [heq]
    exact (canonical1794 hH).trans (sound944 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1649 + (injectiveMoment H (mergeFirst pivotMatrix1649 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1649 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1649 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1649 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1649, value477, value939, value944, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1650 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1650 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound1650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1650 = Sparse.eval value1650 (momentVector H) := by
  have heq : pivotMatrix1650 = (fun u v => node1650 (pivotPermutation1650 u) v) := by apply Matrix.ext; unfold pivotMatrix1650 node1650 pivotPermutation1650; decide +kernel
  have hmoment : injectiveMoment H node1650 = injectiveMoment H pivotMatrix1650 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1650 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1650 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1650 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1650 (0 : Fin 4) = raw3415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1650 raw3415; decide +kernel
    rw [heq]
    exact (canonical3415 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1650 (1 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1650 (1 : Fin 4) = raw1964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1650 raw1964; decide +kernel
    rw [heq]
    exact (canonical1964 hH).trans (sound806 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1650 (2 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1650 (2 : Fin 4) = raw1791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1650 raw1791; decide +kernel
    rw [heq]
    exact (canonical1791 hH).trans (sound474 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1650 (3 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1650 (3 : Fin 4) = raw1784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1650 raw1784; decide +kernel
    rw [heq]
    exact (canonical1784 hH).trans (sound975 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1650 + (injectiveMoment H (mergeFirst pivotMatrix1650 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1650 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1650 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1650 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1650, value1057, value474, value806, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1651 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1651 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

theorem sound1651 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1651 = Sparse.eval value1651 (momentVector H) := by
  have heq : pivotMatrix1651 = (fun u v => node1651 (pivotPermutation1651 u) v) := by apply Matrix.ext; unfold pivotMatrix1651 node1651 pivotPermutation1651; decide +kernel
  have hmoment : injectiveMoment H node1651 = injectiveMoment H pivotMatrix1651 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1651 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1651 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1651 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1651 (0 : Fin 4) = raw3420 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1651 raw3420; decide +kernel
    rw [heq]
    exact (canonical3420 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1651 (1 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1651 (1 : Fin 4) = raw1977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1651 raw1977; decide +kernel
    rw [heq]
    exact (canonical1977 hH).trans (sound804 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1651 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1651 (2 : Fin 4) = raw1795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1651 raw1795; decide +kernel
    rw [heq]
    exact (canonical1795 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1651 (3 : Fin 4)) =
      Sparse.eval value475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1651 (3 : Fin 4) = raw1792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1651 raw1792; decide +kernel
    rw [heq]
    exact (canonical1792 hH).trans (sound475 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1651 + (injectiveMoment H (mergeFirst pivotMatrix1651 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1651 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1651 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1651 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1651, value1010, value475, value476, value804, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1652 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1652 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound1652 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1652 = Sparse.eval value1652 (momentVector H) := by
  have heq : pivotMatrix1652 = (fun u v => node1652 (pivotPermutation1652 u) v) := by apply Matrix.ext; unfold pivotMatrix1652 node1652 pivotPermutation1652; decide +kernel
  have hmoment : injectiveMoment H node1652 = injectiveMoment H pivotMatrix1652 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1652 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1652 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1652 (0 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1652 (0 : Fin 4) = raw3421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1652 raw3421; decide +kernel
    rw [heq]
    exact (canonical3421 hH).trans (sound1000 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1652 (1 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1652 (1 : Fin 4) = raw1978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1652 raw1978; decide +kernel
    rw [heq]
    exact (canonical1978 hH).trans (sound805 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1652 (2 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1652 (2 : Fin 4) = raw1796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1652 raw1796; decide +kernel
    rw [heq]
    exact (canonical1796 hH).trans (sound477 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1652 (3 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1652 (3 : Fin 4) = raw1793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1652 raw1793; decide +kernel
    rw [heq]
    exact (canonical1793 hH).trans (sound1277 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1652 + (injectiveMoment H (mergeFirst pivotMatrix1652 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1652 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1652 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1652 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1652, value1000, value1277, value477, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1653 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1653 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound1653 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1653 = Sparse.eval value1653 (momentVector H) := by
  have heq : pivotMatrix1653 = (fun u v => node1653 (pivotPermutation1653 u) v) := by apply Matrix.ext; unfold pivotMatrix1653 node1653 pivotPermutation1653; decide +kernel
  have hmoment : injectiveMoment H node1653 = injectiveMoment H pivotMatrix1653 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1653 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1653 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1653 (0 : Fin 4)) =
      Sparse.eval value1002 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1653 (0 : Fin 4) = raw3422 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1653 raw3422; decide +kernel
    rw [heq]
    exact (canonical3422 hH).trans (sound1002 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1653 (1 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1653 (1 : Fin 4) = raw1979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1653 raw1979; decide +kernel
    rw [heq]
    exact (canonical1979 hH).trans (sound802 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1653 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1653 (2 : Fin 4) = raw1797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1653 raw1797; decide +kernel
    rw [heq]
    exact (canonical1797 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1653 (3 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1653 (3 : Fin 4) = raw1794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1653 raw1794; decide +kernel
    rw [heq]
    exact (canonical1794 hH).trans (sound944 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1653 + (injectiveMoment H (mergeFirst pivotMatrix1653 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1653 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1653 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1653 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1653, value1002, value476, value802, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1654 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1654 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound1654 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1654 = Sparse.eval value1654 (momentVector H) := by
  have heq : pivotMatrix1654 = (fun u v => node1654 (pivotPermutation1654 u) v) := by apply Matrix.ext; unfold pivotMatrix1654 node1654 pivotPermutation1654; decide +kernel
  have hmoment : injectiveMoment H node1654 = injectiveMoment H pivotMatrix1654 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1654 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1654 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1654 (0 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (0 : Fin 4) = raw6414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw6414; decide +kernel
    rw [heq]
    exact (canonical6414 hH).trans (sound1008 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1654 (1 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (1 : Fin 4) = raw2123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw2123; decide +kernel
    rw [heq]
    exact (canonical2123 hH).trans (sound1190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1654 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (2 : Fin 4) = raw1798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw1798; decide +kernel
    rw [heq]
    exact (canonical1798 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1654 (3 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1654 (3 : Fin 4) = raw1786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1654 raw1786; decide +kernel
    rw [heq]
    exact (canonical1786 hH).trans (sound472 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1654 + (injectiveMoment H (mergeFirst pivotMatrix1654 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1654 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1654 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1654 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1654, value1008, value1190, value472, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1655 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1655 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound1655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1655 = Sparse.eval value1655 (momentVector H) := by
  have heq : pivotMatrix1655 = (fun u v => node1655 (pivotPermutation1655 u) v) := by apply Matrix.ext; unfold pivotMatrix1655 node1655 pivotPermutation1655; decide +kernel
  have hmoment : injectiveMoment H node1655 = injectiveMoment H pivotMatrix1655 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1655 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1655 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1655 (0 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1655 (0 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1655 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1655 (1 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1655 (1 : Fin 4) = raw2120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1655 raw2120; decide +kernel
    rw [heq]
    exact (canonical2120 hH).trans (sound939 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1655 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1655 (2 : Fin 4) = raw1798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1655 raw1798; decide +kernel
    rw [heq]
    exact (canonical1798 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1655 (3 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1655 (3 : Fin 4) = raw1788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1655 raw1788; decide +kernel
    rw [heq]
    exact (canonical1788 hH).trans (sound473 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1655 + (injectiveMoment H (mergeFirst pivotMatrix1655 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1655 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1655 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1655 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1655, value473, value939, value944, value945, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1656 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1656 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem sound1656 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1656 = Sparse.eval value1656 (momentVector H) := by
  have heq : pivotMatrix1656 = (fun u v => node1656 (pivotPermutation1656 u) v) := by apply Matrix.ext; unfold pivotMatrix1656 node1656 pivotPermutation1656; decide +kernel
  have hmoment : injectiveMoment H node1656 = injectiveMoment H pivotMatrix1656 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1656 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1656 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1656 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1656 (0 : Fin 4) = raw6416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1656 raw6416; decide +kernel
    rw [heq]
    exact (canonical6416 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1656 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1656 (1 : Fin 4) = raw2125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1656 raw2125; decide +kernel
    rw [heq]
    exact (canonical2125 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1656 (2 : Fin 4)) =
      Sparse.eval value475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1656 (2 : Fin 4) = raw1800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1656 raw1800; decide +kernel
    rw [heq]
    exact (canonical1800 hH).trans (sound475 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1656 (3 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1656 (3 : Fin 4) = raw1791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1656 raw1791; decide +kernel
    rw [heq]
    exact (canonical1791 hH).trans (sound474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1656 + (injectiveMoment H (mergeFirst pivotMatrix1656 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1656 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1656 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1656 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1656, value1010, value474, value475, value496, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1657 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1657 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound1657 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1657 = Sparse.eval value1657 (momentVector H) := by
  have heq : pivotMatrix1657 = (fun u v => node1657 (pivotPermutation1657 u) v) := by apply Matrix.ext; unfold pivotMatrix1657 node1657 pivotPermutation1657; decide +kernel
  have hmoment : injectiveMoment H node1657 = injectiveMoment H pivotMatrix1657 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1657 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1657 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1657 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (0 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1657 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (1 : Fin 4) = raw2121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw2121; decide +kernel
    rw [heq]
    exact (canonical2121 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1657 (2 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (2 : Fin 4) = raw1799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw1799; decide +kernel
    rw [heq]
    exact (canonical1799 hH).trans (sound1277 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1657 (3 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (3 : Fin 4) = raw1791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw1791; decide +kernel
    rw [heq]
    exact (canonical1791 hH).trans (sound474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1657 + (injectiveMoment H (mergeFirst pivotMatrix1657 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1657 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1657 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1657 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1657, value1079, value1277, value474, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1658 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1658 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 0, -3]]

theorem sound1658 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1658 = Sparse.eval value1658 (momentVector H) := by
  have heq : pivotMatrix1658 = (fun u v => node1658 (pivotPermutation1658 u) v) := by apply Matrix.ext; unfold pivotMatrix1658 node1658 pivotPermutation1658; decide +kernel
  have hmoment : injectiveMoment H node1658 = injectiveMoment H pivotMatrix1658 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1658 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1658 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1658 (0 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1658 (0 : Fin 4) = raw2228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1658 raw2228; decide +kernel
    rw [heq]
    exact (canonical2228 hH).trans (sound483 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1658 (1 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1658 (1 : Fin 4) = raw1859 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1658 raw1859; decide +kernel
    rw [heq]
    exact (canonical1859 hH).trans (sound1094 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1658 (2 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1658 (2 : Fin 4) = raw1817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1658 raw1817; decide +kernel
    rw [heq]
    exact (canonical1817 hH).trans (sound479 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1658 (3 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1658 (3 : Fin 4) = raw1816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1658 raw1816; decide +kernel
    rw [heq]
    exact (canonical1816 hH).trans (sound460 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1658 + (injectiveMoment H (mergeFirst pivotMatrix1658 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1658 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1658 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1658 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1658, value1094, value460, value479, value483, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1659 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1659 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem sound1659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1659 = Sparse.eval value1659 (momentVector H) := by
  have heq : pivotMatrix1659 = (fun u v => node1659 (pivotPermutation1659 u) v) := by apply Matrix.ext; unfold pivotMatrix1659 node1659 pivotPermutation1659; decide +kernel
  have hmoment : injectiveMoment H node1659 = injectiveMoment H pivotMatrix1659 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1659 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1659 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1659 (0 : Fin 4)) =
      Sparse.eval value789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1659 (0 : Fin 4) = raw5645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1659 raw5645; decide +kernel
    rw [heq]
    exact (canonical5645 hH).trans (sound789 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1659 (1 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1659 (1 : Fin 4) = raw2118 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1659 raw2118; decide +kernel
    rw [heq]
    exact (canonical2118 hH).trans (sound479 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1659 (2 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1659 (2 : Fin 4) = raw1817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1659 raw1817; decide +kernel
    rw [heq]
    exact (canonical1817 hH).trans (sound479 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1659 (3 : Fin 4)) =
      Sparse.eval value789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1659 (3 : Fin 4) = raw1804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1659 raw1804; decide +kernel
    rw [heq]
    exact (canonical1804 hH).trans (sound789 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1659 + (injectiveMoment H (mergeFirst pivotMatrix1659 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1659 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1659 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1659 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1659, value479, value789, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1660 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1660 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem sound1660 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1660 = Sparse.eval value1660 (momentVector H) := by
  have heq : pivotMatrix1660 = (fun u v => node1660 (pivotPermutation1660 u) v) := by apply Matrix.ext; unfold pivotMatrix1660 node1660 pivotPermutation1660; decide +kernel
  have hmoment : injectiveMoment H node1660 = injectiveMoment H pivotMatrix1660 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1660 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1660 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1660 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1660 (0 : Fin 4) = raw3436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1660 raw3436; decide +kernel
    rw [heq]
    exact (canonical3436 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1660 (1 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1660 (1 : Fin 4) = raw1992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1660 raw1992; decide +kernel
    rw [heq]
    exact (canonical1992 hH).trans (sound484 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1660 (2 : Fin 4)) =
      Sparse.eval value478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1660 (2 : Fin 4) = raw1815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1660 raw1815; decide +kernel
    rw [heq]
    exact (canonical1815 hH).trans (sound478 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1660 (3 : Fin 4)) =
      Sparse.eval value794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1660 (3 : Fin 4) = raw1810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1660 raw1810; decide +kernel
    rw [heq]
    exact (canonical1810 hH).trans (sound794 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1660 + (injectiveMoment H (mergeFirst pivotMatrix1660 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1660 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1660 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1660 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1660, value1059, value478, value484, value794, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1661 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1661 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem sound1661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1661 = Sparse.eval value1661 (momentVector H) := by
  have heq : pivotMatrix1661 = (fun u v => node1661 (pivotPermutation1661 u) v) := by apply Matrix.ext; unfold pivotMatrix1661 node1661 pivotPermutation1661; decide +kernel
  have hmoment : injectiveMoment H node1661 = injectiveMoment H pivotMatrix1661 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1661 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1661 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1661 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (0 : Fin 4) = raw3449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw3449; decide +kernel
    rw [heq]
    exact (canonical3449 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1661 (1 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (1 : Fin 4) = raw2000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw2000; decide +kernel
    rw [heq]
    exact (canonical2000 hH).trans (sound488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1661 (2 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (2 : Fin 4) = raw1818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw1818; decide +kernel
    rw [heq]
    exact (canonical1818 hH).trans (sound791 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1661 (3 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1661 (3 : Fin 4) = raw1817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1661 raw1817; decide +kernel
    rw [heq]
    exact (canonical1817 hH).trans (sound479 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1661 + (injectiveMoment H (mergeFirst pivotMatrix1661 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1661 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1661 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1661 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1661, value1059, value479, value488, value791, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1662 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1662 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2]]

theorem sound1662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1662 = Sparse.eval value1662 (momentVector H) := by
  have heq : pivotMatrix1662 = (fun u v => node1662 (pivotPermutation1662 u) v) := by apply Matrix.ext; unfold pivotMatrix1662 node1662 pivotPermutation1662; decide +kernel
  have hmoment : injectiveMoment H node1662 = injectiveMoment H pivotMatrix1662 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1662 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1662 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1662 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (0 : Fin 4) = raw6434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw6434; decide +kernel
    rw [heq]
    exact (canonical6434 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1662 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (1 : Fin 4) = raw2127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw2127; decide +kernel
    rw [heq]
    exact (canonical2127 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1662 (2 : Fin 4)) =
      Sparse.eval value479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (2 : Fin 4) = raw1819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw1819; decide +kernel
    rw [heq]
    exact (canonical1819 hH).trans (sound479 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1662 (3 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1662 (3 : Fin 4) = raw1813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1662 raw1813; decide +kernel
    rw [heq]
    exact (canonical1813 hH).trans (sound406 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1662 + (injectiveMoment H (mergeFirst pivotMatrix1662 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1662 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1662 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1662 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1662, value406, value479, value496, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1663 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1663 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem sound1663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1663 = Sparse.eval value1663 (momentVector H) := by
  have heq : pivotMatrix1663 = (fun u v => node1663 (pivotPermutation1663 u) v) := by apply Matrix.ext; unfold pivotMatrix1663 node1663 pivotPermutation1663; decide +kernel
  have hmoment : injectiveMoment H node1663 = injectiveMoment H pivotMatrix1663 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1663 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1663 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1663 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1663 (0 : Fin 4) = raw6435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1663 raw6435; decide +kernel
    rw [heq]
    exact (canonical6435 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1663 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1663 (1 : Fin 4) = raw2128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1663 raw2128; decide +kernel
    rw [heq]
    exact (canonical2128 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1663 (2 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1663 (2 : Fin 4) = raw1820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1663 raw1820; decide +kernel
    rw [heq]
    exact (canonical1820 hH).trans (sound460 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1663 (3 : Fin 4)) =
      Sparse.eval value478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1663 (3 : Fin 4) = raw1815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1663 raw1815; decide +kernel
    rw [heq]
    exact (canonical1815 hH).trans (sound478 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1663 + (injectiveMoment H (mergeFirst pivotMatrix1663 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1663 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1663 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1663 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1663, value1036, value460, value478, value495, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
