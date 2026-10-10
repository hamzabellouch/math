import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical53
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical99
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical100
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1664 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1664 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

theorem sound1664 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1664 = Sparse.eval value1664 (momentVector H) := by
  have heq : pivotMatrix1664 = (fun u v => node1664 (pivotPermutation1664 u) v) := by apply Matrix.ext; unfold pivotMatrix1664 node1664 pivotPermutation1664; decide +kernel
  have hmoment : injectiveMoment H node1664 = injectiveMoment H pivotMatrix1664 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1664 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1664 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1664 (0 : Fin 4)) =
      Sparse.eval value1364 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1664 (0 : Fin 4) = raw1523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1664 raw1523; decide +kernel
    rw [heq]
    exact (canonical1523 hH).trans (sound1364 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1664 (1 : Fin 4)) =
      Sparse.eval value478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1664 (1 : Fin 4) = raw1815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1664 raw1815; decide +kernel
    rw [heq]
    exact (canonical1815 hH).trans (sound478 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1664 (2 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1664 (2 : Fin 4) = raw1852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1664 raw1852; decide +kernel
    rw [heq]
    exact (canonical1852 hH).trans (sound832 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1664 (3 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1664 (3 : Fin 4) = raw1856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1664 raw1856; decide +kernel
    rw [heq]
    exact (canonical1856 hH).trans (sound816 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1664 + (injectiveMoment H (mergeFirst pivotMatrix1664 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1664 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1664 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1664 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1664, value1364, value478, value816, value832, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1665 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1665 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

theorem sound1665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1665 = Sparse.eval value1665 (momentVector H) := by
  have heq : pivotMatrix1665 = (fun u v => node1665 (pivotPermutation1665 u) v) := by apply Matrix.ext; unfold pivotMatrix1665 node1665 pivotPermutation1665; decide +kernel
  have hmoment : injectiveMoment H node1665 = injectiveMoment H pivotMatrix1665 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1665 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1665 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1665 (0 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1665 (0 : Fin 4) = raw1611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1665 raw1611; decide +kernel
    rw [heq]
    exact (canonical1611 hH).trans (sound894 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1665 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1665 (1 : Fin 4) = raw1868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1665 raw1868; decide +kernel
    rw [heq]
    exact (canonical1868 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1665 (2 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1665 (2 : Fin 4) = raw1934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1665 raw1934; decide +kernel
    rw [heq]
    exact (canonical1934 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1665 (3 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1665 (3 : Fin 4) = raw1935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1665 raw1935; decide +kernel
    rw [heq]
    exact (canonical1935 hH).trans (sound943 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1665 + (injectiveMoment H (mergeFirst pivotMatrix1665 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1665 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1665 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1665 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1665, value1207, value261, value894, value943, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1666 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1666 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem sound1666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1666 = Sparse.eval value1666 (momentVector H) := by
  have heq : pivotMatrix1666 = (fun u v => node1666 (pivotPermutation1666 u) v) := by apply Matrix.ext; unfold pivotMatrix1666 node1666 pivotPermutation1666; decide +kernel
  have hmoment : injectiveMoment H node1666 = injectiveMoment H pivotMatrix1666 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1666 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1666 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1666 (0 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1666 (0 : Fin 4) = raw1639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1666 raw1639; decide +kernel
    rw [heq]
    exact (canonical1639 hH).trans (sound1234 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1666 (1 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1666 (1 : Fin 4) = raw1934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1666 raw1934; decide +kernel
    rw [heq]
    exact (canonical1934 hH).trans (sound1207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1666 (2 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1666 (2 : Fin 4) = raw1975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1666 raw1975; decide +kernel
    rw [heq]
    exact (canonical1975 hH).trans (sound483 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1666 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1666 (3 : Fin 4) = raw1976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1666 raw1976; decide +kernel
    rw [heq]
    exact (canonical1976 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1666 + (injectiveMoment H (mergeFirst pivotMatrix1666 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1666 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1666 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1666 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1666, value1207, value1234, value1235, value483, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1667 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1667 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

theorem sound1667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1667 = Sparse.eval value1667 (momentVector H) := by
  have heq : pivotMatrix1667 = (fun u v => node1667 (pivotPermutation1667 u) v) := by apply Matrix.ext; unfold pivotMatrix1667 node1667 pivotPermutation1667; decide +kernel
  have hmoment : injectiveMoment H node1667 = injectiveMoment H pivotMatrix1667 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1667 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1667 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1667 (0 : Fin 4)) =
      Sparse.eval value957 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1667 (0 : Fin 4) = raw1654 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1667 raw1654; decide +kernel
    rw [heq]
    exact (canonical1654 hH).trans (sound957 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1667 (1 : Fin 4)) =
      Sparse.eval value792 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1667 (1 : Fin 4) = raw1986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1667 raw1986; decide +kernel
    rw [heq]
    exact (canonical1986 hH).trans (sound792 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1667 (2 : Fin 4)) =
      Sparse.eval value792 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1667 (2 : Fin 4) = raw2015 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1667 raw2015; decide +kernel
    rw [heq]
    exact (canonical2015 hH).trans (sound792 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1667 (3 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1667 (3 : Fin 4) = raw2023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1667 raw2023; decide +kernel
    rw [heq]
    exact (canonical2023 hH).trans (sound1028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1667 + (injectiveMoment H (mergeFirst pivotMatrix1667 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1667 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1667 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1667 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1667, value1028, value792, value957, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1668 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1668 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

theorem sound1668 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1668 = Sparse.eval value1668 (momentVector H) := by
  have heq : pivotMatrix1668 = (fun u v => node1668 (pivotPermutation1668 u) v) := by apply Matrix.ext; unfold pivotMatrix1668 node1668 pivotPermutation1668; decide +kernel
  have hmoment : injectiveMoment H node1668 = injectiveMoment H pivotMatrix1668 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1668 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1668 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1668 (0 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1668 (0 : Fin 4) = raw1662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1668 raw1662; decide +kernel
    rw [heq]
    exact (canonical1662 hH).trans (sound1306 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1668 (1 : Fin 4)) =
      Sparse.eval value485 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1668 (1 : Fin 4) = raw1995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1668 raw1995; decide +kernel
    rw [heq]
    exact (canonical1995 hH).trans (sound485 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1668 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1668 (2 : Fin 4) = raw2033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1668 raw2033; decide +kernel
    rw [heq]
    exact (canonical2033 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1668 (3 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1668 (3 : Fin 4) = raw2038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1668 raw2038; decide +kernel
    rw [heq]
    exact (canonical2038 hH).trans (sound1066 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1668 + (injectiveMoment H (mergeFirst pivotMatrix1668 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1668 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1668 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1668 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1668, value1066, value1079, value1306, value485, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1669 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1669 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound1669 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1669 = Sparse.eval value1669 (momentVector H) := by
  have heq : pivotMatrix1669 = (fun u v => node1669 (pivotPermutation1669 u) v) := by apply Matrix.ext; unfold pivotMatrix1669 node1669 pivotPermutation1669; decide +kernel
  have hmoment : injectiveMoment H node1669 = injectiveMoment H pivotMatrix1669 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1669 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1669 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1669 (0 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1669 (0 : Fin 4) = raw1705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1669 raw1705; decide +kernel
    rw [heq]
    exact (canonical1705 hH).trans (sound1080 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1669 (1 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1669 (1 : Fin 4) = raw2081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1669 raw2081; decide +kernel
    rw [heq]
    exact (canonical2081 hH).trans (sound1081 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1669 (2 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1669 (2 : Fin 4) = raw2087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1669 raw2087; decide +kernel
    rw [heq]
    exact (canonical2087 hH).trans (sound491 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1669 (3 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1669 (3 : Fin 4) = raw2088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1669 raw2088; decide +kernel
    rw [heq]
    exact (canonical2088 hH).trans (sound1066 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1669 + (injectiveMoment H (mergeFirst pivotMatrix1669 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1669 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1669 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1669 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1669, value1066, value1080, value1081, value491, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1670 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1670 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem sound1670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1670 = Sparse.eval value1670 (momentVector H) := by
  have heq : pivotMatrix1670 = (fun u v => node1670 (pivotPermutation1670 u) v) := by apply Matrix.ext; unfold pivotMatrix1670 node1670 pivotPermutation1670; decide +kernel
  have hmoment : injectiveMoment H node1670 = injectiveMoment H pivotMatrix1670 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1670 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1670 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1670 (0 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1670 (0 : Fin 4) = raw1723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1670 raw1723; decide +kernel
    rw [heq]
    exact (canonical1723 hH).trans (sound1234 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1670 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1670 (1 : Fin 4) = raw2107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1670 raw2107; decide +kernel
    rw [heq]
    exact (canonical2107 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1670 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1670 (2 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1670 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1670 (3 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1670 (3 : Fin 4) = raw2111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1670 raw2111; decide +kernel
    rw [heq]
    exact (canonical2111 hH).trans (sound496 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1670 + (injectiveMoment H (mergeFirst pivotMatrix1670 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1670 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1670 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1670 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1670, value1016, value1079, value1234, value496, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1671 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1671 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1671 = Sparse.eval value1671 (momentVector H) := by
  have heq : pivotMatrix1671 = (fun u v => node1671 (pivotPermutation1671 u) v) := by apply Matrix.ext; unfold pivotMatrix1671 node1671 pivotPermutation1671; decide +kernel
  have hmoment : injectiveMoment H node1671 = injectiveMoment H pivotMatrix1671 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1671 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1671 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1671 (0 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1671 (0 : Fin 4) = raw1727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1671 raw1727; decide +kernel
    rw [heq]
    exact (canonical1727 hH).trans (sound1080 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1671 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1671 (1 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1671 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1671 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1671 (2 : Fin 4) = raw2113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1671 raw2113; decide +kernel
    rw [heq]
    exact (canonical2113 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1671 (3 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1671 (3 : Fin 4) = raw2114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1671 raw2114; decide +kernel
    rw [heq]
    exact (canonical2114 hH).trans (sound495 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1671 + (injectiveMoment H (mergeFirst pivotMatrix1671 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1671 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1671 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1671 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1671, value1063, value1079, value1080, value495, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1672 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1672 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem sound1672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1672 = Sparse.eval value1672 (momentVector H) := by
  have heq : pivotMatrix1672 = (fun u v => node1672 (pivotPermutation1672 u) v) := by apply Matrix.ext; unfold pivotMatrix1672 node1672 pivotPermutation1672; decide +kernel
  have hmoment : injectiveMoment H node1672 = injectiveMoment H pivotMatrix1672 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1672 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1672 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1672 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1672 (0 : Fin 4) = raw2346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1672 raw2346; decide +kernel
    rw [heq]
    exact (canonical2346 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1672 (1 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1672 (1 : Fin 4) = raw1967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1672 raw1967; decide +kernel
    rw [heq]
    exact (canonical1967 hH).trans (sound474 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1672 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1672 (2 : Fin 4) = raw1924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1672 raw1924; decide +kernel
    rw [heq]
    exact (canonical1924 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1672 (3 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1672 (3 : Fin 4) = raw1919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1672 raw1919; decide +kernel
    rw [heq]
    exact (canonical1919 hH).trans (sound1223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1672 + (injectiveMoment H (mergeFirst pivotMatrix1672 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1672 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1672 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1672 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1672, value1010, value1223, value474, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1673 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1673 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem sound1673 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1673 = Sparse.eval value1673 (momentVector H) := by
  have heq : pivotMatrix1673 = (fun u v => node1673 (pivotPermutation1673 u) v) := by apply Matrix.ext; unfold pivotMatrix1673 node1673 pivotPermutation1673; decide +kernel
  have hmoment : injectiveMoment H node1673 = injectiveMoment H pivotMatrix1673 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1673 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1673 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1673 (0 : Fin 4)) =
      Sparse.eval value1333 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1673 (0 : Fin 4) = raw2357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1673 raw2357; decide +kernel
    rw [heq]
    exact (canonical2357 hH).trans (sound1333 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1673 (1 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1673 (1 : Fin 4) = raw1975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1673 raw1975; decide +kernel
    rw [heq]
    exact (canonical1975 hH).trans (sound483 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1673 (2 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1673 (2 : Fin 4) = raw1934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1673 raw1934; decide +kernel
    rw [heq]
    exact (canonical1934 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1673 (3 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1673 (3 : Fin 4) = raw1933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1673 raw1933; decide +kernel
    rw [heq]
    exact (canonical1933 hH).trans (sound1094 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1673 + (injectiveMoment H (mergeFirst pivotMatrix1673 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1673 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1673 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1673 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1673, value1094, value1207, value1333, value483, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1674 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1674 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem sound1674 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1674 = Sparse.eval value1674 (momentVector H) := by
  have heq : pivotMatrix1674 = (fun u v => node1674 (pivotPermutation1674 u) v) := by apply Matrix.ext; unfold pivotMatrix1674 node1674 pivotPermutation1674; decide +kernel
  have hmoment : injectiveMoment H node1674 = injectiveMoment H pivotMatrix1674 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1674 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1674 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1674 (0 : Fin 4)) =
      Sparse.eval value1247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1674 (0 : Fin 4) = raw2358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1674 raw2358; decide +kernel
    rw [heq]
    exact (canonical2358 hH).trans (sound1247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1674 (1 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1674 (1 : Fin 4) = raw1976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1674 raw1976; decide +kernel
    rw [heq]
    exact (canonical1976 hH).trans (sound1235 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1674 (2 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1674 (2 : Fin 4) = raw1935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1674 raw1935; decide +kernel
    rw [heq]
    exact (canonical1935 hH).trans (sound943 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1674 (3 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1674 (3 : Fin 4) = raw1934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1674 raw1934; decide +kernel
    rw [heq]
    exact (canonical1934 hH).trans (sound1207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1674 + (injectiveMoment H (mergeFirst pivotMatrix1674 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1674 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1674 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1674 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1674, value1207, value1235, value1247, value943, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1675 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1675 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem sound1675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1675 = Sparse.eval value1675 (momentVector H) := by
  have heq : pivotMatrix1675 = (fun u v => node1675 (pivotPermutation1675 u) v) := by apply Matrix.ext; unfold pivotMatrix1675 node1675 pivotPermutation1675; decide +kernel
  have hmoment : injectiveMoment H node1675 = injectiveMoment H pivotMatrix1675 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1675 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1675 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1675 (0 : Fin 4)) =
      Sparse.eval value829 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1675 (0 : Fin 4) = raw2393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1675 raw2393; decide +kernel
    rw [heq]
    exact (canonical2393 hH).trans (sound829 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1675 (1 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1675 (1 : Fin 4) = raw2023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1675 raw2023; decide +kernel
    rw [heq]
    exact (canonical2023 hH).trans (sound1028 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1675 (2 : Fin 4)) =
      Sparse.eval value1120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1675 (2 : Fin 4) = raw1990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1675 raw1990; decide +kernel
    rw [heq]
    exact (canonical1990 hH).trans (sound1120 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1675 (3 : Fin 4)) =
      Sparse.eval value792 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1675 (3 : Fin 4) = raw1986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1675 raw1986; decide +kernel
    rw [heq]
    exact (canonical1986 hH).trans (sound792 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1675 + (injectiveMoment H (mergeFirst pivotMatrix1675 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1675 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1675 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1675 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1675, value1028, value1120, value792, value829, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1676 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1676 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem sound1676 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1676 = Sparse.eval value1676 (momentVector H) := by
  have heq : pivotMatrix1676 = (fun u v => node1676 (pivotPermutation1676 u) v) := by apply Matrix.ext; unfold pivotMatrix1676 node1676 pivotPermutation1676; decide +kernel
  have hmoment : injectiveMoment H node1676 = injectiveMoment H pivotMatrix1676 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1676 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1676 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1676 (0 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1676 (0 : Fin 4) = raw2397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1676 raw2397; decide +kernel
    rw [heq]
    exact (canonical2397 hH).trans (sound1111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1676 (1 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1676 (1 : Fin 4) = raw2029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1676 raw2029; decide +kernel
    rw [heq]
    exact (canonical2029 hH).trans (sound1109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1676 (2 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1676 (2 : Fin 4) = raw1992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1676 raw1992; decide +kernel
    rw [heq]
    exact (canonical1992 hH).trans (sound484 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1676 (3 : Fin 4)) =
      Sparse.eval value1120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1676 (3 : Fin 4) = raw1990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1676 raw1990; decide +kernel
    rw [heq]
    exact (canonical1990 hH).trans (sound1120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1676 + (injectiveMoment H (mergeFirst pivotMatrix1676 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1676 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1676 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1676 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1676, value1109, value1111, value1120, value484, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1677 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1677 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem sound1677 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1677 = Sparse.eval value1677 (momentVector H) := by
  have heq : pivotMatrix1677 = (fun u v => node1677 (pivotPermutation1677 u) v) := by apply Matrix.ext; unfold pivotMatrix1677 node1677 pivotPermutation1677; decide +kernel
  have hmoment : injectiveMoment H node1677 = injectiveMoment H pivotMatrix1677 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1677 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1677 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1677 (0 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1677 (0 : Fin 4) = raw2399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1677 raw2399; decide +kernel
    rw [heq]
    exact (canonical2399 hH).trans (sound510 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1677 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1677 (1 : Fin 4) = raw2033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1677 raw2033; decide +kernel
    rw [heq]
    exact (canonical2033 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1677 (2 : Fin 4)) =
      Sparse.eval value485 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1677 (2 : Fin 4) = raw1995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1677 raw1995; decide +kernel
    rw [heq]
    exact (canonical1995 hH).trans (sound485 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1677 (3 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1677 (3 : Fin 4) = raw1992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1677 raw1992; decide +kernel
    rw [heq]
    exact (canonical1992 hH).trans (sound484 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1677 + (injectiveMoment H (mergeFirst pivotMatrix1677 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1677 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1677 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1677 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1677, value1079, value484, value485, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1678 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1678 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound1678 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1678 = Sparse.eval value1678 (momentVector H) := by
  have heq : pivotMatrix1678 = (fun u v => node1678 (pivotPermutation1678 u) v) := by apply Matrix.ext; unfold pivotMatrix1678 node1678 pivotPermutation1678; decide +kernel
  have hmoment : injectiveMoment H node1678 = injectiveMoment H pivotMatrix1678 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1678 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1678 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1678 (0 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1678 (0 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1678 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1678 (1 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1678 (1 : Fin 4) = raw2043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1678 raw2043; decide +kernel
    rw [heq]
    exact (canonical2043 hH).trans (sound1268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1678 (2 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1678 (2 : Fin 4) = raw1999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1678 raw1999; decide +kernel
    rw [heq]
    exact (canonical1999 hH).trans (sound487 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1678 (3 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1678 (3 : Fin 4) = raw1998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1678 raw1998; decide +kernel
    rw [heq]
    exact (canonical1998 hH).trans (sound1306 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1678 + (injectiveMoment H (mergeFirst pivotMatrix1678 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1678 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1678 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1678 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1678, value1249, value1268, value1306, value487, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1679 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1679 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem sound1679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1679 = Sparse.eval value1679 (momentVector H) := by
  have heq : pivotMatrix1679 = (fun u v => node1679 (pivotPermutation1679 u) v) := by apply Matrix.ext; unfold pivotMatrix1679 node1679 pivotPermutation1679; decide +kernel
  have hmoment : injectiveMoment H node1679 = injectiveMoment H pivotMatrix1679 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1679 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1679 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1679 (0 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1679 (0 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1679 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1679 (1 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1679 (1 : Fin 4) = raw2044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1679 raw2044; decide +kernel
    rw [heq]
    exact (canonical2044 hH).trans (sound1099 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1679 (2 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1679 (2 : Fin 4) = raw2000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1679 raw2000; decide +kernel
    rw [heq]
    exact (canonical2000 hH).trans (sound488 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1679 (3 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1679 (3 : Fin 4) = raw1999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1679 raw1999; decide +kernel
    rw [heq]
    exact (canonical1999 hH).trans (sound487 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1679 + (injectiveMoment H (mergeFirst pivotMatrix1679 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1679 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1679 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1679 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1679, value1099, value487, value488, value513, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1680 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1680 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem sound1680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1680 = Sparse.eval value1680 (momentVector H) := by
  have heq : pivotMatrix1680 = (fun u v => node1680 (pivotPermutation1680 u) v) := by apply Matrix.ext; unfold pivotMatrix1680 node1680 pivotPermutation1680; decide +kernel
  have hmoment : injectiveMoment H node1680 = injectiveMoment H pivotMatrix1680 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1680 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1680 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1680 (0 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1680 (0 : Fin 4) = raw2419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1680 raw2419; decide +kernel
    rw [heq]
    exact (canonical2419 hH).trans (sound1107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1680 (1 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1680 (1 : Fin 4) = raw2058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1680 raw2058; decide +kernel
    rw [heq]
    exact (canonical2058 hH).trans (sound1109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1680 (2 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1680 (2 : Fin 4) = raw2029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1680 raw2029; decide +kernel
    rw [heq]
    exact (canonical2029 hH).trans (sound1109 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1680 (3 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1680 (3 : Fin 4) = raw2023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1680 raw2023; decide +kernel
    rw [heq]
    exact (canonical2023 hH).trans (sound1028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1680 + (injectiveMoment H (mergeFirst pivotMatrix1680 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1680 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1680 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1680 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1680, value1028, value1107, value1109, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1681 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1681 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem sound1681 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1681 = Sparse.eval value1681 (momentVector H) := by
  have heq : pivotMatrix1681 = (fun u v => node1681 (pivotPermutation1681 u) v) := by apply Matrix.ext; unfold pivotMatrix1681 node1681 pivotPermutation1681; decide +kernel
  have hmoment : injectiveMoment H node1681 = injectiveMoment H pivotMatrix1681 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1681 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1681 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1681 (0 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1681 (0 : Fin 4) = raw2428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1681 raw2428; decide +kernel
    rw [heq]
    exact (canonical2428 hH).trans (sound1112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1681 (1 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1681 (1 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1681 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1681 (2 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1681 (2 : Fin 4) = raw2038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1681 raw2038; decide +kernel
    rw [heq]
    exact (canonical2038 hH).trans (sound1066 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1681 (3 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1681 (3 : Fin 4) = raw2033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1681 raw2033; decide +kernel
    rw [heq]
    exact (canonical2033 hH).trans (sound1079 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1681 + (injectiveMoment H (mergeFirst pivotMatrix1681 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1681 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1681 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1681 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1681, value1066, value1079, value1112, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1682 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1682 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound1682 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1682 = Sparse.eval value1682 (momentVector H) := by
  have heq : pivotMatrix1682 = (fun u v => node1682 (pivotPermutation1682 u) v) := by apply Matrix.ext; unfold pivotMatrix1682 node1682 pivotPermutation1682; decide +kernel
  have hmoment : injectiveMoment H node1682 = injectiveMoment H pivotMatrix1682 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1682 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1682 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1682 (0 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1682 (0 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1682 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1682 (1 : Fin 4)) =
      Sparse.eval value933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1682 (1 : Fin 4) = raw2068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1682 raw2068; decide +kernel
    rw [heq]
    exact (canonical2068 hH).trans (sound933 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1682 (2 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1682 (2 : Fin 4) = raw2043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1682 raw2043; decide +kernel
    rw [heq]
    exact (canonical2043 hH).trans (sound1268 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1682 (3 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1682 (3 : Fin 4) = raw2042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1682 raw2042; decide +kernel
    rw [heq]
    exact (canonical2042 hH).trans (sound1080 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1682 + (injectiveMoment H (mergeFirst pivotMatrix1682 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1682 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1682 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1682 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1682, value1080, value1123, value1268, value933, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1683 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1683 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound1683 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1683 = Sparse.eval value1683 (momentVector H) := by
  have heq : pivotMatrix1683 = (fun u v => node1683 (pivotPermutation1683 u) v) := by apply Matrix.ext; unfold pivotMatrix1683 node1683 pivotPermutation1683; decide +kernel
  have hmoment : injectiveMoment H node1683 = injectiveMoment H pivotMatrix1683 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1683 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1683 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1683 (0 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1683 (0 : Fin 4) = raw2435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1683 raw2435; decide +kernel
    rw [heq]
    exact (canonical2435 hH).trans (sound1096 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1683 (1 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1683 (1 : Fin 4) = raw2069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1683 raw2069; decide +kernel
    rw [heq]
    exact (canonical2069 hH).trans (sound936 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1683 (2 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1683 (2 : Fin 4) = raw2045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1683 raw2045; decide +kernel
    rw [heq]
    exact (canonical2045 hH).trans (sound1013 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1683 (3 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1683 (3 : Fin 4) = raw2044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1683 raw2044; decide +kernel
    rw [heq]
    exact (canonical2044 hH).trans (sound1099 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1683 + (injectiveMoment H (mergeFirst pivotMatrix1683 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1683 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1683 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1683 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1683, value1013, value1096, value1099, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1684 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1684 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

theorem sound1684 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1684 = Sparse.eval value1684 (momentVector H) := by
  have heq : pivotMatrix1684 = (fun u v => node1684 (pivotPermutation1684 u) v) := by apply Matrix.ext; unfold pivotMatrix1684 node1684 pivotPermutation1684; decide +kernel
  have hmoment : injectiveMoment H node1684 = injectiveMoment H pivotMatrix1684 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1684 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1684 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1684 (0 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (0 : Fin 4) = raw2455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2455; decide +kernel
    rw [heq]
    exact (canonical2455 hH).trans (sound842 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1684 (1 : Fin 4)) =
      Sparse.eval value489 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (1 : Fin 4) = raw2079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2079; decide +kernel
    rw [heq]
    exact (canonical2079 hH).trans (sound489 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1684 (2 : Fin 4)) =
      Sparse.eval value726 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (2 : Fin 4) = raw2067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2067; decide +kernel
    rw [heq]
    exact (canonical2067 hH).trans (sound726 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1684 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1684 (3 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1684 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1684 + (injectiveMoment H (mergeFirst pivotMatrix1684 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1684 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1684 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1684 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1684, value489, value726, value805, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1685 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1685 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound1685 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1685 = Sparse.eval value1685 (momentVector H) := by
  have heq : pivotMatrix1685 = (fun u v => node1685 (pivotPermutation1685 u) v) := by apply Matrix.ext; unfold pivotMatrix1685 node1685 pivotPermutation1685; decide +kernel
  have hmoment : injectiveMoment H node1685 = injectiveMoment H pivotMatrix1685 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1685 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1685 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1685 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1685 (0 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1685 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1685 (1 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1685 (1 : Fin 4) = raw2082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1685 raw2082; decide +kernel
    rw [heq]
    exact (canonical2082 hH).trans (sound490 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1685 (2 : Fin 4)) =
      Sparse.eval value1098 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1685 (2 : Fin 4) = raw2070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1685 raw2070; decide +kernel
    rw [heq]
    exact (canonical2070 hH).trans (sound1098 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1685 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1685 (3 : Fin 4) = raw2069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1685 raw2069; decide +kernel
    rw [heq]
    exact (canonical2069 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1685 + (injectiveMoment H (mergeFirst pivotMatrix1685 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1685 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1685 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1685 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1685, value1078, value1098, value490, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1686 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1686 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound1686 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1686 = Sparse.eval value1686 (momentVector H) := by
  have heq : pivotMatrix1686 = (fun u v => node1686 (pivotPermutation1686 u) v) := by apply Matrix.ext; unfold pivotMatrix1686 node1686 pivotPermutation1686; decide +kernel
  have hmoment : injectiveMoment H node1686 = injectiveMoment H pivotMatrix1686 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1686 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1686 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1686 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1686 (0 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1686 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1686 (1 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1686 (1 : Fin 4) = raw2088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1686 raw2088; decide +kernel
    rw [heq]
    exact (canonical2088 hH).trans (sound1066 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1686 (2 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1686 (2 : Fin 4) = raw2082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1686 raw2082; decide +kernel
    rw [heq]
    exact (canonical2082 hH).trans (sound490 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1686 (3 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1686 (3 : Fin 4) = raw2081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1686 raw2081; decide +kernel
    rw [heq]
    exact (canonical2081 hH).trans (sound1081 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1686 + (injectiveMoment H (mergeFirst pivotMatrix1686 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1686 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1686 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1686 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1686, value1058, value1066, value1081, value490, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1687 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1687 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound1687 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1687 = Sparse.eval value1687 (momentVector H) := by
  have heq : pivotMatrix1687 = (fun u v => node1687 (pivotPermutation1687 u) v) := by apply Matrix.ext; unfold pivotMatrix1687 node1687 pivotPermutation1687; decide +kernel
  have hmoment : injectiveMoment H node1687 = injectiveMoment H pivotMatrix1687 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1687 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1687 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1687 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1687 (0 : Fin 4) = raw2485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1687 raw2485; decide +kernel
    rw [heq]
    exact (canonical2485 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1687 (1 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1687 (1 : Fin 4) = raw2105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1687 raw2105; decide +kernel
    rw [heq]
    exact (canonical2105 hH).trans (sound1003 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1687 (2 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1687 (2 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1687 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1687 (3 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1687 (3 : Fin 4) = raw2099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1687 raw2099; decide +kernel
    rw [heq]
    exact (canonical2099 hH).trans (sound1269 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1687 + (injectiveMoment H (mergeFirst pivotMatrix1687 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1687 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1687 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1687 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1687, value1003, value1010, value1269, value476, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1688 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1688 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound1688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1688 = Sparse.eval value1688 (momentVector H) := by
  have heq : pivotMatrix1688 = (fun u v => node1688 (pivotPermutation1688 u) v) := by apply Matrix.ext; unfold pivotMatrix1688 node1688 pivotPermutation1688; decide +kernel
  have hmoment : injectiveMoment H node1688 = injectiveMoment H pivotMatrix1688 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1688 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1688 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1688 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (0 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1688 (1 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (1 : Fin 4) = raw2106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2106; decide +kernel
    rw [heq]
    exact (canonical2106 hH).trans (sound939 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1688 (2 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (2 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1688 (3 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1688 (3 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1688 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1688 + (injectiveMoment H (mergeFirst pivotMatrix1688 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1688 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1688 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1688 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1688, value1005, value1190, value476, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1689 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1689 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem sound1689 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1689 = Sparse.eval value1689 (momentVector H) := by
  have heq : pivotMatrix1689 = (fun u v => node1689 (pivotPermutation1689 u) v) := by apply Matrix.ext; unfold pivotMatrix1689 node1689 pivotPermutation1689; decide +kernel
  have hmoment : injectiveMoment H node1689 = injectiveMoment H pivotMatrix1689 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1689 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1689 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1689 (0 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1689 (0 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1689 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1689 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1689 (1 : Fin 4) = raw2109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1689 raw2109; decide +kernel
    rw [heq]
    exact (canonical2109 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1689 (2 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1689 (2 : Fin 4) = raw2105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1689 raw2105; decide +kernel
    rw [heq]
    exact (canonical2105 hH).trans (sound1003 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1689 (3 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1689 (3 : Fin 4) = raw2104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1689 raw2104; decide +kernel
    rw [heq]
    exact (canonical2104 hH).trans (sound495 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1689 + (injectiveMoment H (mergeFirst pivotMatrix1689 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1689 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1689 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1689 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1689, value1003, value1036, value495, value517, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1690 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1690 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1690 = Sparse.eval value1690 (momentVector H) := by
  have heq : pivotMatrix1690 = (fun u v => node1690 (pivotPermutation1690 u) v) := by apply Matrix.ext; unfold pivotMatrix1690 node1690 pivotPermutation1690; decide +kernel
  have hmoment : injectiveMoment H node1690 = injectiveMoment H pivotMatrix1690 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1690 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1690 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1690 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1690 (0 : Fin 4) = raw2491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1690 raw2491; decide +kernel
    rw [heq]
    exact (canonical2491 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1690 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1690 (1 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1690 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1690 (2 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1690 (2 : Fin 4) = raw2107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1690 raw2107; decide +kernel
    rw [heq]
    exact (canonical2107 hH).trans (sound1016 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1690 (3 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1690 (3 : Fin 4) = raw2106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1690 raw2106; decide +kernel
    rw [heq]
    exact (canonical2106 hH).trans (sound939 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1690 + (injectiveMoment H (mergeFirst pivotMatrix1690 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1690 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1690 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1690 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1690, value1016, value1078, value1079, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1691 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1691 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem sound1691 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1691 = Sparse.eval value1691 (momentVector H) := by
  have heq : pivotMatrix1691 = (fun u v => node1691 (pivotPermutation1691 u) v) := by apply Matrix.ext; unfold pivotMatrix1691 node1691 pivotPermutation1691; decide +kernel
  have hmoment : injectiveMoment H node1691 = injectiveMoment H pivotMatrix1691 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1691 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1691 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1691 (0 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1691 (0 : Fin 4) = raw2496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1691 raw2496; decide +kernel
    rw [heq]
    exact (canonical2496 hH).trans (sound510 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1691 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1691 (1 : Fin 4) = raw2114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1691 raw2114; decide +kernel
    rw [heq]
    exact (canonical2114 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1691 (2 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1691 (2 : Fin 4) = raw2111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1691 raw2111; decide +kernel
    rw [heq]
    exact (canonical2111 hH).trans (sound496 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1691 (3 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1691 (3 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1691 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1691 + (injectiveMoment H (mergeFirst pivotMatrix1691 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1691 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1691 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1691 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1691, value1079, value495, value496, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1692 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1692 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

theorem sound1692 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1692 = Sparse.eval value1692 (momentVector H) := by
  have heq : pivotMatrix1692 = (fun u v => node1692 (pivotPermutation1692 u) v) := by apply Matrix.ext; unfold pivotMatrix1692 node1692 pivotPermutation1692; decide +kernel
  have hmoment : injectiveMoment H node1692 = injectiveMoment H pivotMatrix1692 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1692 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1692 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1692 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1692 (0 : Fin 4) = raw3136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1692 raw3136; decide +kernel
    rw [heq]
    exact (canonical3136 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1692 (1 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1692 (1 : Fin 4) = raw2074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1692 raw2074; decide +kernel
    rw [heq]
    exact (canonical2074 hH).trans (sound484 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1692 (2 : Fin 4)) =
      Sparse.eval value480 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1692 (2 : Fin 4) = raw1965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1692 raw1965; decide +kernel
    rw [heq]
    exact (canonical1965 hH).trans (sound480 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1692 (3 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1692 (3 : Fin 4) = raw1949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1692 raw1949; decide +kernel
    rw [heq]
    exact (canonical1949 hH).trans (sound808 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1692 + (injectiveMoment H (mergeFirst pivotMatrix1692 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1692 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1692 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1692 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1692, value1315, value480, value484, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1693 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1693 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

theorem sound1693 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1693 = Sparse.eval value1693 (momentVector H) := by
  have heq : pivotMatrix1693 = (fun u v => node1693 (pivotPermutation1693 u) v) := by apply Matrix.ext; unfold pivotMatrix1693 node1693 pivotPermutation1693; decide +kernel
  have hmoment : injectiveMoment H node1693 = injectiveMoment H pivotMatrix1693 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1693 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1693 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1693 (0 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1693 (0 : Fin 4) = raw3498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1693 raw3498; decide +kernel
    rw [heq]
    exact (canonical3498 hH).trans (sound1314 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1693 (1 : Fin 4)) =
      Sparse.eval value485 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1693 (1 : Fin 4) = raw2085 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1693 raw2085; decide +kernel
    rw [heq]
    exact (canonical2085 hH).trans (sound485 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1693 (2 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1693 (2 : Fin 4) = raw1967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1693 raw1967; decide +kernel
    rw [heq]
    exact (canonical1967 hH).trans (sound474 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1693 (3 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1693 (3 : Fin 4) = raw1949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1693 raw1949; decide +kernel
    rw [heq]
    exact (canonical1949 hH).trans (sound808 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1693 + (injectiveMoment H (mergeFirst pivotMatrix1693 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1693 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1693 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1693 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1693, value1314, value474, value485, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1694 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1694 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem sound1694 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1694 = Sparse.eval value1694 (momentVector H) := by
  have heq : pivotMatrix1694 = (fun u v => node1694 (pivotPermutation1694 u) v) := by apply Matrix.ext; unfold pivotMatrix1694 node1694 pivotPermutation1694; decide +kernel
  have hmoment : injectiveMoment H node1694 = injectiveMoment H pivotMatrix1694 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1694 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1694 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1694 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1694 (0 : Fin 4) = raw5687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1694 raw5687; decide +kernel
    rw [heq]
    exact (canonical5687 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1694 (1 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1694 (1 : Fin 4) = raw2122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1694 raw2122; decide +kernel
    rw [heq]
    exact (canonical2122 hH).trans (sound488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1694 (2 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1694 (2 : Fin 4) = raw1977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1694 raw1977; decide +kernel
    rw [heq]
    exact (canonical1977 hH).trans (sound804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1694 (3 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1694 (3 : Fin 4) = raw1949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1694 raw1949; decide +kernel
    rw [heq]
    exact (canonical1949 hH).trans (sound808 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1694 + (injectiveMoment H (mergeFirst pivotMatrix1694 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1694 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1694 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1694 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1694, value488, value804, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1695 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1695 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem sound1695 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1695 = Sparse.eval value1695 (momentVector H) := by
  have heq : pivotMatrix1695 = (fun u v => node1695 (pivotPermutation1695 u) v) := by apply Matrix.ext; unfold pivotMatrix1695 node1695 pivotPermutation1695; decide +kernel
  have hmoment : injectiveMoment H node1695 = injectiveMoment H pivotMatrix1695 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1695 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1695 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1695 (0 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1695 (0 : Fin 4) = raw3141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1695 raw3141; decide +kernel
    rw [heq]
    exact (canonical3141 hH).trans (sound1301 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1695 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1695 (1 : Fin 4) = raw2076 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1695 raw2076; decide +kernel
    rw [heq]
    exact (canonical2076 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1695 (2 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1695 (2 : Fin 4) = raw1967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1695 raw1967; decide +kernel
    rw [heq]
    exact (canonical1967 hH).trans (sound474 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1695 (3 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1695 (3 : Fin 4) = raw1958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1695 raw1958; decide +kernel
    rw [heq]
    exact (canonical1958 hH).trans (sound807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1695 + (injectiveMoment H (mergeFirst pivotMatrix1695 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1695 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1695 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1695 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1695, value1079, value1301, value474, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1696 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1696 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem sound1696 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1696 = Sparse.eval value1696 (momentVector H) := by
  have heq : pivotMatrix1696 = (fun u v => node1696 (pivotPermutation1696 u) v) := by apply Matrix.ext; unfold pivotMatrix1696 node1696 pivotPermutation1696; decide +kernel
  have hmoment : injectiveMoment H node1696 = injectiveMoment H pivotMatrix1696 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1696 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1696 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1696 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1696 (0 : Fin 4) = raw3146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1696 raw3146; decide +kernel
    rw [heq]
    exact (canonical3146 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1696 (1 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1696 (1 : Fin 4) = raw2078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1696 raw2078; decide +kernel
    rw [heq]
    exact (canonical2078 hH).trans (sound805 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1696 (2 : Fin 4)) =
      Sparse.eval value481 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1696 (2 : Fin 4) = raw1970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1696 raw1970; decide +kernel
    rw [heq]
    exact (canonical1970 hH).trans (sound481 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1696 (3 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1696 (3 : Fin 4) = raw1964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1696 raw1964; decide +kernel
    rw [heq]
    exact (canonical1964 hH).trans (sound806 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1696 + (injectiveMoment H (mergeFirst pivotMatrix1696 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1696 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1696 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1696 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1696, value481, value805, value806, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1697 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1697 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound1697 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1697 = Sparse.eval value1697 (momentVector H) := by
  have heq : pivotMatrix1697 = (fun u v => node1697 (pivotPermutation1697 u) v) := by apply Matrix.ext; unfold pivotMatrix1697 node1697 pivotPermutation1697; decide +kernel
  have hmoment : injectiveMoment H node1697 = injectiveMoment H pivotMatrix1697 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1697 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1697 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1697 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1697 (0 : Fin 4) = raw3155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1697 raw3155; decide +kernel
    rw [heq]
    exact (canonical3155 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1697 (1 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1697 (1 : Fin 4) = raw2080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1697 raw2080; decide +kernel
    rw [heq]
    exact (canonical2080 hH).trans (sound995 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1697 (2 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1697 (2 : Fin 4) = raw1977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1697 raw1977; decide +kernel
    rw [heq]
    exact (canonical1977 hH).trans (sound804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1697 (3 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1697 (3 : Fin 4) = raw1975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1697 raw1975; decide +kernel
    rw [heq]
    exact (canonical1975 hH).trans (sound483 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1697 + (injectiveMoment H (mergeFirst pivotMatrix1697 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1697 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1697 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1697 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1697, value1036, value483, value804, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1698 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1698 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound1698 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1698 = Sparse.eval value1698 (momentVector H) := by
  have heq : pivotMatrix1698 = (fun u v => node1698 (pivotPermutation1698 u) v) := by apply Matrix.ext; unfold pivotMatrix1698 node1698 pivotPermutation1698; decide +kernel
  have hmoment : injectiveMoment H node1698 = injectiveMoment H pivotMatrix1698 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1698 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1698 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1698 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1698 (0 : Fin 4) = raw3156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1698 raw3156; decide +kernel
    rw [heq]
    exact (canonical3156 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1698 (1 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1698 (1 : Fin 4) = raw2081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1698 raw2081; decide +kernel
    rw [heq]
    exact (canonical2081 hH).trans (sound1081 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1698 (2 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1698 (2 : Fin 4) = raw1978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1698 raw1978; decide +kernel
    rw [heq]
    exact (canonical1978 hH).trans (sound805 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1698 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1698 (3 : Fin 4) = raw1976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1698 raw1976; decide +kernel
    rw [heq]
    exact (canonical1976 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1698 + (injectiveMoment H (mergeFirst pivotMatrix1698 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1698 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1698 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1698 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1698, value1079, value1081, value1235, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1699 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1699 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem sound1699 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1699 = Sparse.eval value1699 (momentVector H) := by
  have heq : pivotMatrix1699 = (fun u v => node1699 (pivotPermutation1699 u) v) := by apply Matrix.ext; unfold pivotMatrix1699 node1699 pivotPermutation1699; decide +kernel
  have hmoment : injectiveMoment H node1699 = injectiveMoment H pivotMatrix1699 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1699 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1699 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1699 (0 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1699 (0 : Fin 4) = raw3503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1699 raw3503; decide +kernel
    rw [heq]
    exact (canonical3503 hH).trans (sound854 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1699 (1 : Fin 4)) =
      Sparse.eval value726 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1699 (1 : Fin 4) = raw2086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1699 raw2086; decide +kernel
    rw [heq]
    exact (canonical2086 hH).trans (sound726 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1699 (2 : Fin 4)) =
      Sparse.eval value482 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1699 (2 : Fin 4) = raw1974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1699 raw1974; decide +kernel
    rw [heq]
    exact (canonical1974 hH).trans (sound482 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1699 (3 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1699 (3 : Fin 4) = raw1964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1699 raw1964; decide +kernel
    rw [heq]
    exact (canonical1964 hH).trans (sound806 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1699 + (injectiveMoment H (mergeFirst pivotMatrix1699 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1699 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1699 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1699 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1699, value482, value726, value806, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1700 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1700 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem sound1700 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1700 = Sparse.eval value1700 (momentVector H) := by
  have heq : pivotMatrix1700 = (fun u v => node1700 (pivotPermutation1700 u) v) := by apply Matrix.ext; unfold pivotMatrix1700 node1700 pivotPermutation1700; decide +kernel
  have hmoment : injectiveMoment H node1700 = injectiveMoment H pivotMatrix1700 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1700 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1700 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1700 (0 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1700 (0 : Fin 4) = raw3506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1700 raw3506; decide +kernel
    rw [heq]
    exact (canonical3506 hH).trans (sound1112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1700 (1 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1700 (1 : Fin 4) = raw2087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1700 raw2087; decide +kernel
    rw [heq]
    exact (canonical2087 hH).trans (sound491 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1700 (2 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1700 (2 : Fin 4) = raw1978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1700 raw1978; decide +kernel
    rw [heq]
    exact (canonical1978 hH).trans (sound805 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1700 (3 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1700 (3 : Fin 4) = raw1975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1700 raw1975; decide +kernel
    rw [heq]
    exact (canonical1975 hH).trans (sound483 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1700 + (injectiveMoment H (mergeFirst pivotMatrix1700 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1700 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1700 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1700 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1700, value1112, value483, value491, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1701 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1701 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound1701 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1701 = Sparse.eval value1701 (momentVector H) := by
  have heq : pivotMatrix1701 = (fun u v => node1701 (pivotPermutation1701 u) v) := by apply Matrix.ext; unfold pivotMatrix1701 node1701 pivotPermutation1701; decide +kernel
  have hmoment : injectiveMoment H node1701 = injectiveMoment H pivotMatrix1701 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1701 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1701 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1701 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1701 (0 : Fin 4) = raw3507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1701 raw3507; decide +kernel
    rw [heq]
    exact (canonical3507 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1701 (1 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1701 (1 : Fin 4) = raw2088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1701 raw2088; decide +kernel
    rw [heq]
    exact (canonical2088 hH).trans (sound1066 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1701 (2 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1701 (2 : Fin 4) = raw1979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1701 raw1979; decide +kernel
    rw [heq]
    exact (canonical1979 hH).trans (sound802 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1701 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1701 (3 : Fin 4) = raw1976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1701 raw1976; decide +kernel
    rw [heq]
    exact (canonical1976 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1701 + (injectiveMoment H (mergeFirst pivotMatrix1701 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1701 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1701 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1701 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1701, value1057, value1066, value1235, value802, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1702 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1702 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound1702 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1702 = Sparse.eval value1702 (momentVector H) := by
  have heq : pivotMatrix1702 = (fun u v => node1702 (pivotPermutation1702 u) v) := by apply Matrix.ext; unfold pivotMatrix1702 node1702 pivotPermutation1702; decide +kernel
  have hmoment : injectiveMoment H node1702 = injectiveMoment H pivotMatrix1702 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1702 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1702 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1702 (0 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1702 (0 : Fin 4) = raw5692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1702 raw5692; decide +kernel
    rw [heq]
    exact (canonical5692 hH).trans (sound806 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1702 (1 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1702 (1 : Fin 4) = raw2123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1702 raw2123; decide +kernel
    rw [heq]
    exact (canonical2123 hH).trans (sound1190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1702 (2 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1702 (2 : Fin 4) = raw1980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1702 raw1980; decide +kernel
    rw [heq]
    exact (canonical1980 hH).trans (sound802 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1702 (3 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1702 (3 : Fin 4) = raw1967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1702 raw1967; decide +kernel
    rw [heq]
    exact (canonical1967 hH).trans (sound474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1702 + (injectiveMoment H (mergeFirst pivotMatrix1702 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1702 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1702 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1702 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1702, value1190, value474, value802, value806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1703 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1703 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem sound1703 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1703 = Sparse.eval value1703 (momentVector H) := by
  have heq : pivotMatrix1703 = (fun u v => node1703 (pivotPermutation1703 u) v) := by apply Matrix.ext; unfold pivotMatrix1703 node1703 pivotPermutation1703; decide +kernel
  have hmoment : injectiveMoment H node1703 = injectiveMoment H pivotMatrix1703 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1703 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1703 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1703 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1703 (0 : Fin 4) = raw6508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1703 raw6508; decide +kernel
    rw [heq]
    exact (canonical6508 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1703 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1703 (1 : Fin 4) = raw2130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1703 raw2130; decide +kernel
    rw [heq]
    exact (canonical2130 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1703 (2 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1703 (2 : Fin 4) = raw1983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1703 raw1983; decide +kernel
    rw [heq]
    exact (canonical1983 hH).trans (sound483 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1703 (3 : Fin 4)) =
      Sparse.eval value481 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1703 (3 : Fin 4) = raw1970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1703 raw1970; decide +kernel
    rw [heq]
    exact (canonical1970 hH).trans (sound481 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1703 + (injectiveMoment H (mergeFirst pivotMatrix1703 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1703 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1703 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1703 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1703, value1058, value481, value483, value495, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1704 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1704 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound1704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1704 = Sparse.eval value1704 (momentVector H) := by
  have heq : pivotMatrix1704 = (fun u v => node1704 (pivotPermutation1704 u) v) := by apply Matrix.ext; unfold pivotMatrix1704 node1704 pivotPermutation1704; decide +kernel
  have hmoment : injectiveMoment H node1704 = injectiveMoment H pivotMatrix1704 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1704 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1704 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1704 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1704 (0 : Fin 4) = raw5693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1704 raw5693; decide +kernel
    rw [heq]
    exact (canonical5693 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1704 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1704 (1 : Fin 4) = raw2124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1704 raw2124; decide +kernel
    rw [heq]
    exact (canonical2124 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1704 (2 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1704 (2 : Fin 4) = raw1981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1704 raw1981; decide +kernel
    rw [heq]
    exact (canonical1981 hH).trans (sound805 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1704 (3 : Fin 4)) =
      Sparse.eval value481 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1704 (3 : Fin 4) = raw1970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1704 raw1970; decide +kernel
    rw [heq]
    exact (canonical1970 hH).trans (sound481 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1704 + (injectiveMoment H (mergeFirst pivotMatrix1704 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1704 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1704 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1704 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1704, value1016, value481, value805, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1705 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1705 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem sound1705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1705 = Sparse.eval value1705 (momentVector H) := by
  have heq : pivotMatrix1705 = (fun u v => node1705 (pivotPermutation1705 u) v) := by apply Matrix.ext; unfold pivotMatrix1705 node1705 pivotPermutation1705; decide +kernel
  have hmoment : injectiveMoment H node1705 = injectiveMoment H pivotMatrix1705 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1705 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1705 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1705 (0 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1705 (0 : Fin 4) = raw6291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1705 raw6291; decide +kernel
    rw [heq]
    exact (canonical6291 hH).trans (sound976 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1705 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1705 (1 : Fin 4) = raw2129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1705 raw2129; decide +kernel
    rw [heq]
    exact (canonical2129 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1705 (2 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1705 (2 : Fin 4) = raw1983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1705 raw1983; decide +kernel
    rw [heq]
    exact (canonical1983 hH).trans (sound483 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1705 (3 : Fin 4)) =
      Sparse.eval value482 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1705 (3 : Fin 4) = raw1974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1705 raw1974; decide +kernel
    rw [heq]
    exact (canonical1974 hH).trans (sound482 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1705 + (injectiveMoment H (mergeFirst pivotMatrix1705 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1705 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1705 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1705 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1705, value1036, value482, value483, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1706 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1706 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem sound1706 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1706 = Sparse.eval value1706 (momentVector H) := by
  have heq : pivotMatrix1706 = (fun u v => node1706 (pivotPermutation1706 u) v) := by apply Matrix.ext; unfold pivotMatrix1706 node1706 pivotPermutation1706; decide +kernel
  have hmoment : injectiveMoment H node1706 = injectiveMoment H pivotMatrix1706 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1706 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1706 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1706 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1706 (0 : Fin 4) = raw5694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1706 raw5694; decide +kernel
    rw [heq]
    exact (canonical5694 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1706 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1706 (1 : Fin 4) = raw2125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1706 raw2125; decide +kernel
    rw [heq]
    exact (canonical2125 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1706 (2 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1706 (2 : Fin 4) = raw1982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1706 raw1982; decide +kernel
    rw [heq]
    exact (canonical1982 hH).trans (sound804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1706 (3 : Fin 4)) =
      Sparse.eval value482 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1706 (3 : Fin 4) = raw1974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1706 raw1974; decide +kernel
    rw [heq]
    exact (canonical1974 hH).trans (sound482 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1706 + (injectiveMoment H (mergeFirst pivotMatrix1706 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1706 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1706 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1706 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1706, value482, value496, value804, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1707 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1707 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound1707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1707 = Sparse.eval value1707 (momentVector H) := by
  have heq : pivotMatrix1707 = (fun u v => node1707 (pivotPermutation1707 u) v) := by apply Matrix.ext; unfold pivotMatrix1707 node1707 pivotPermutation1707; decide +kernel
  have hmoment : injectiveMoment H node1707 = injectiveMoment H pivotMatrix1707 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1707 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1707 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1707 (0 : Fin 4)) =
      Sparse.eval value1307 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1707 (0 : Fin 4) = raw3181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1707 raw3181; decide +kernel
    rw [heq]
    exact (canonical3181 hH).trans (sound1307 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1707 (1 : Fin 4)) =
      Sparse.eval value1158 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1707 (1 : Fin 4) = raw2096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1707 raw2096; decide +kernel
    rw [heq]
    exact (canonical2096 hH).trans (sound1158 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1707 (2 : Fin 4)) =
      Sparse.eval value818 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1707 (2 : Fin 4) = raw2001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1707 raw2001; decide +kernel
    rw [heq]
    exact (canonical2001 hH).trans (sound818 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1707 (3 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1707 (3 : Fin 4) = raw1998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1707 raw1998; decide +kernel
    rw [heq]
    exact (canonical1998 hH).trans (sound1306 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1707 + (injectiveMoment H (mergeFirst pivotMatrix1707 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1707 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1707 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1707 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1707, value1158, value1306, value1307, value818, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1708 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1708 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem sound1708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1708 = Sparse.eval value1708 (momentVector H) := by
  have heq : pivotMatrix1708 = (fun u v => node1708 (pivotPermutation1708 u) v) := by apply Matrix.ext; unfold pivotMatrix1708 node1708 pivotPermutation1708; decide +kernel
  have hmoment : injectiveMoment H node1708 = injectiveMoment H pivotMatrix1708 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1708 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1708 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1708 (0 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1708 (0 : Fin 4) = raw3182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1708 raw3182; decide +kernel
    rw [heq]
    exact (canonical3182 hH).trans (sound1308 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1708 (1 : Fin 4)) =
      Sparse.eval value494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1708 (1 : Fin 4) = raw2097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1708 raw2097; decide +kernel
    rw [heq]
    exact (canonical2097 hH).trans (sound494 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1708 (2 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1708 (2 : Fin 4) = raw2002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1708 raw2002; decide +kernel
    rw [heq]
    exact (canonical2002 hH).trans (sound819 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1708 (3 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1708 (3 : Fin 4) = raw1999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1708 raw1999; decide +kernel
    rw [heq]
    exact (canonical1999 hH).trans (sound487 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1708 + (injectiveMoment H (mergeFirst pivotMatrix1708 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1708 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1708 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1708 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1708, value1308, value487, value494, value819, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1709 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1709 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound1709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1709 = Sparse.eval value1709 (momentVector H) := by
  have heq : pivotMatrix1709 = (fun u v => node1709 (pivotPermutation1709 u) v) := by apply Matrix.ext; unfold pivotMatrix1709 node1709 pivotPermutation1709; decide +kernel
  have hmoment : injectiveMoment H node1709 = injectiveMoment H pivotMatrix1709 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1709 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1709 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1709 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1709 (0 : Fin 4) = raw3544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1709 raw3544; decide +kernel
    rw [heq]
    exact (canonical3544 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1709 (1 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1709 (1 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1709 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1709 (2 : Fin 4)) =
      Sparse.eval value820 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1709 (2 : Fin 4) = raw2003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1709 raw2003; decide +kernel
    rw [heq]
    exact (canonical2003 hH).trans (sound820 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1709 (3 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1709 (3 : Fin 4) = raw1999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1709 raw1999; decide +kernel
    rw [heq]
    exact (canonical1999 hH).trans (sound487 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1709 + (injectiveMoment H (mergeFirst pivotMatrix1709 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1709 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1709 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1709 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1709, value1309, value476, value487, value820, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1710 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1710 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound1710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1710 = Sparse.eval value1710 (momentVector H) := by
  have heq : pivotMatrix1710 = (fun u v => node1710 (pivotPermutation1710 u) v) := by apply Matrix.ext; unfold pivotMatrix1710 node1710 pivotPermutation1710; decide +kernel
  have hmoment : injectiveMoment H node1710 = injectiveMoment H pivotMatrix1710 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1710 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1710 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1710 (0 : Fin 4)) =
      Sparse.eval value1311 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (0 : Fin 4) = raw3545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw3545; decide +kernel
    rw [heq]
    exact (canonical3545 hH).trans (sound1311 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1710 (1 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (1 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1710 (2 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (2 : Fin 4) = raw2004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw2004; decide +kernel
    rw [heq]
    exact (canonical2004 hH).trans (sound819 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1710 (3 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1710 (3 : Fin 4) = raw2000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1710 raw2000; decide +kernel
    rw [heq]
    exact (canonical2000 hH).trans (sound488 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1710 + (injectiveMoment H (mergeFirst pivotMatrix1710 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1710 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1710 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1710 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1710, value1190, value1311, value488, value819, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1711 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1711 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem sound1711 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1711 = Sparse.eval value1711 (momentVector H) := by
  have heq : pivotMatrix1711 = (fun u v => node1711 (pivotPermutation1711 u) v) := by apply Matrix.ext; unfold pivotMatrix1711 node1711 pivotPermutation1711; decide +kernel
  have hmoment : injectiveMoment H node1711 = injectiveMoment H pivotMatrix1711 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1711 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1711 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1711 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1711 (0 : Fin 4) = raw6529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1711 raw6529; decide +kernel
    rw [heq]
    exact (canonical6529 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1711 (1 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1711 (1 : Fin 4) = raw2132 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1711 raw2132; decide +kernel
    rw [heq]
    exact (canonical2132 hH).trans (sound490 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1711 (2 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1711 (2 : Fin 4) = raw2006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1711 raw2006; decide +kernel
    rw [heq]
    exact (canonical2006 hH).trans (sound487 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1711 (3 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1711 (3 : Fin 4) = raw1992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1711 raw1992; decide +kernel
    rw [heq]
    exact (canonical1992 hH).trans (sound484 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1711 + (injectiveMoment H (mergeFirst pivotMatrix1711 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1711 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1711 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1711 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1711, value1078, value484, value487, value490, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1712 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1712 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem sound1712 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1712 = Sparse.eval value1712 (momentVector H) := by
  have heq : pivotMatrix1712 = (fun u v => node1712 (pivotPermutation1712 u) v) := by apply Matrix.ext; unfold pivotMatrix1712 node1712 pivotPermutation1712; decide +kernel
  have hmoment : injectiveMoment H node1712 = injectiveMoment H pivotMatrix1712 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1712 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1712 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1712 (0 : Fin 4)) =
      Sparse.eval value984 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1712 (0 : Fin 4) = raw6302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1712 raw6302; decide +kernel
    rw [heq]
    exact (canonical6302 hH).trans (sound984 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1712 (1 : Fin 4)) =
      Sparse.eval value492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1712 (1 : Fin 4) = raw2131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1712 raw2131; decide +kernel
    rw [heq]
    exact (canonical2131 hH).trans (sound492 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1712 (2 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1712 (2 : Fin 4) = raw2006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1712 raw2006; decide +kernel
    rw [heq]
    exact (canonical2006 hH).trans (sound487 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1712 (3 : Fin 4)) =
      Sparse.eval value485 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1712 (3 : Fin 4) = raw1995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1712 raw1995; decide +kernel
    rw [heq]
    exact (canonical1995 hH).trans (sound485 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1712 + (injectiveMoment H (mergeFirst pivotMatrix1712 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1712 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1712 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1712 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1712, value485, value487, value492, value984, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1713 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1713 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound1713 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1713 = Sparse.eval value1713 (momentVector H) := by
  have heq : pivotMatrix1713 = (fun u v => node1713 (pivotPermutation1713 u) v) := by apply Matrix.ext; unfold pivotMatrix1713 node1713 pivotPermutation1713; decide +kernel
  have hmoment : injectiveMoment H node1713 = injectiveMoment H pivotMatrix1713 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1713 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1713 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1713 (0 : Fin 4)) =
      Sparse.eval value817 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1713 (0 : Fin 4) = raw5704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1713 raw5704; decide +kernel
    rw [heq]
    exact (canonical5704 hH).trans (sound817 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1713 (1 : Fin 4)) =
      Sparse.eval value798 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1713 (1 : Fin 4) = raw2126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1713 raw2126; decide +kernel
    rw [heq]
    exact (canonical2126 hH).trans (sound798 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1713 (2 : Fin 4)) =
      Sparse.eval value818 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1713 (2 : Fin 4) = raw2005 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1713 raw2005; decide +kernel
    rw [heq]
    exact (canonical2005 hH).trans (sound818 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1713 (3 : Fin 4)) =
      Sparse.eval value486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1713 (3 : Fin 4) = raw1997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1713 raw1997; decide +kernel
    rw [heq]
    exact (canonical1997 hH).trans (sound486 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1713 + (injectiveMoment H (mergeFirst pivotMatrix1713 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1713 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1713 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1713 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1713, value486, value798, value817, value818, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1714 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1714 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem sound1714 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1714 = Sparse.eval value1714 (momentVector H) := by
  have heq : pivotMatrix1714 = (fun u v => node1714 (pivotPermutation1714 u) v) := by apply Matrix.ext; unfold pivotMatrix1714 node1714 pivotPermutation1714; decide +kernel
  have hmoment : injectiveMoment H node1714 = injectiveMoment H pivotMatrix1714 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1714 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1714 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1714 (0 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1714 (0 : Fin 4) = raw3217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1714 raw3217; decide +kernel
    rw [heq]
    exact (canonical3217 hH).trans (sound985 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1714 (1 : Fin 4)) =
      Sparse.eval value486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1714 (1 : Fin 4) = raw2098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1714 raw2098; decide +kernel
    rw [heq]
    exact (canonical2098 hH).trans (sound486 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1714 (2 : Fin 4)) =
      Sparse.eval value817 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1714 (2 : Fin 4) = raw2047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1714 raw2047; decide +kernel
    rw [heq]
    exact (canonical2047 hH).trans (sound817 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1714 (3 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1714 (3 : Fin 4) = raw2042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1714 raw2042; decide +kernel
    rw [heq]
    exact (canonical2042 hH).trans (sound1080 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1714 + (injectiveMoment H (mergeFirst pivotMatrix1714 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1714 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1714 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1714 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1714, value1080, value486, value817, value985, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1715 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1715 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound1715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1715 = Sparse.eval value1715 (momentVector H) := by
  have heq : pivotMatrix1715 = (fun u v => node1715 (pivotPermutation1715 u) v) := by apply Matrix.ext; unfold pivotMatrix1715 node1715 pivotPermutation1715; decide +kernel
  have hmoment : injectiveMoment H node1715 = injectiveMoment H pivotMatrix1715 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1715 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1715 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1715 (0 : Fin 4)) =
      Sparse.eval value1299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1715 (0 : Fin 4) = raw3219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1715 raw3219; decide +kernel
    rw [heq]
    exact (canonical3219 hH).trans (sound1299 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1715 (1 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1715 (1 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1715 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1715 (2 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1715 (2 : Fin 4) = raw2049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1715 raw2049; decide +kernel
    rw [heq]
    exact (canonical2049 hH).trans (sound1202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1715 (3 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1715 (3 : Fin 4) = raw2044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1715 raw2044; decide +kernel
    rw [heq]
    exact (canonical2044 hH).trans (sound1099 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1715 + (injectiveMoment H (mergeFirst pivotMatrix1715 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1715 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1715 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1715 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1715, value1099, value1202, value1299, value476, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1716 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1716 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound1716 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1716 = Sparse.eval value1716 (momentVector H) := by
  have heq : pivotMatrix1716 = (fun u v => node1716 (pivotPermutation1716 u) v) := by apply Matrix.ext; unfold pivotMatrix1716 node1716 pivotPermutation1716; decide +kernel
  have hmoment : injectiveMoment H node1716 = injectiveMoment H pivotMatrix1716 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1716 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1716 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1716 (0 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1716 (0 : Fin 4) = raw3220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1716 raw3220; decide +kernel
    rw [heq]
    exact (canonical3220 hH).trans (sound1206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1716 (1 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1716 (1 : Fin 4) = raw2101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1716 raw2101; decide +kernel
    rw [heq]
    exact (canonical2101 hH).trans (sound1190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1716 (2 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1716 (2 : Fin 4) = raw2050 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1716 raw2050; decide +kernel
    rw [heq]
    exact (canonical2050 hH).trans (sound1202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1716 (3 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1716 (3 : Fin 4) = raw2045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1716 raw2045; decide +kernel
    rw [heq]
    exact (canonical2045 hH).trans (sound1013 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1716 + (injectiveMoment H (mergeFirst pivotMatrix1716 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1716 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1716 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1716 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1716, value1013, value1190, value1202, value1206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1717 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1717 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound1717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1717 = Sparse.eval value1717 (momentVector H) := by
  have heq : pivotMatrix1717 = (fun u v => node1717 (pivotPermutation1717 u) v) := by apply Matrix.ext; unfold pivotMatrix1717 node1717 pivotPermutation1717; decide +kernel
  have hmoment : injectiveMoment H node1717 = injectiveMoment H pivotMatrix1717 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1717 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1717 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1717 (0 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1717 (0 : Fin 4) = raw3221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1717 raw3221; decide +kernel
    rw [heq]
    exact (canonical3221 hH).trans (sound977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1717 (1 : Fin 4)) =
      Sparse.eval value812 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1717 (1 : Fin 4) = raw2102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1717 raw2102; decide +kernel
    rw [heq]
    exact (canonical2102 hH).trans (sound812 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1717 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1717 (2 : Fin 4) = raw2051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1717 raw2051; decide +kernel
    rw [heq]
    exact (canonical2051 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1717 (3 : Fin 4)) =
      Sparse.eval value809 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1717 (3 : Fin 4) = raw2046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1717 raw2046; decide +kernel
    rw [heq]
    exact (canonical2046 hH).trans (sound809 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1717 + (injectiveMoment H (mergeFirst pivotMatrix1717 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1717 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1717 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1717 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1717, value1063, value809, value812, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1718 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1718 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem sound1718 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1718 = Sparse.eval value1718 (momentVector H) := by
  have heq : pivotMatrix1718 = (fun u v => node1718 (pivotPermutation1718 u) v) := by apply Matrix.ext; unfold pivotMatrix1718 node1718 pivotPermutation1718; decide +kernel
  have hmoment : injectiveMoment H node1718 = injectiveMoment H pivotMatrix1718 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1718 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1718 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1718 (0 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1718 (0 : Fin 4) = raw3235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1718 raw3235; decide +kernel
    rw [heq]
    exact (canonical3235 hH).trans (sound1207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1718 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1718 (1 : Fin 4) = raw2107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1718 raw2107; decide +kernel
    rw [heq]
    exact (canonical2107 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1718 (2 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1718 (2 : Fin 4) = raw2072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1718 raw2072; decide +kernel
    rw [heq]
    exact (canonical2072 hH).trans (sound1203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1718 (3 : Fin 4)) =
      Sparse.eval value1098 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1718 (3 : Fin 4) = raw2070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1718 raw2070; decide +kernel
    rw [heq]
    exact (canonical2070 hH).trans (sound1098 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1718 + (injectiveMoment H (mergeFirst pivotMatrix1718 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1718 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1718 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1718 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1718, value1016, value1098, value1203, value1207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1719 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1719 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1719 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1719 = Sparse.eval value1719 (momentVector H) := by
  have heq : pivotMatrix1719 = (fun u v => node1719 (pivotPermutation1719 u) v) := by apply Matrix.ext; unfold pivotMatrix1719 node1719 pivotPermutation1719; decide +kernel
  have hmoment : injectiveMoment H node1719 = injectiveMoment H pivotMatrix1719 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1719 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1719 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1719 (0 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1719 (0 : Fin 4) = raw3244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1719 raw3244; decide +kernel
    rw [heq]
    exact (canonical3244 hH).trans (sound1081 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1719 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1719 (1 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1719 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1719 (2 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1719 (2 : Fin 4) = raw2084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1719 raw2084; decide +kernel
    rw [heq]
    exact (canonical2084 hH).trans (sound1043 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1719 (3 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1719 (3 : Fin 4) = raw2082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1719 raw2082; decide +kernel
    rw [heq]
    exact (canonical2082 hH).trans (sound490 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1719 + (injectiveMoment H (mergeFirst pivotMatrix1719 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1719 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1719 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1719 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1719, value1043, value1079, value1081, value490, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1720 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1720 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound1720 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1720 = Sparse.eval value1720 (momentVector H) := by
  have heq : pivotMatrix1720 = (fun u v => node1720 (pivotPermutation1720 u) v) := by apply Matrix.ext; unfold pivotMatrix1720 node1720 pivotPermutation1720; decide +kernel
  have hmoment : injectiveMoment H node1720 = injectiveMoment H pivotMatrix1720 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1720 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1720 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1720 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1720 (0 : Fin 4) = raw3250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1720 raw3250; decide +kernel
    rw [heq]
    exact (canonical3250 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1720 (1 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1720 (1 : Fin 4) = raw2113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1720 raw2113; decide +kernel
    rw [heq]
    exact (canonical2113 hH).trans (sound1063 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1720 (2 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1720 (2 : Fin 4) = raw2090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1720 raw2090; decide +kernel
    rw [heq]
    exact (canonical2090 hH).trans (sound1041 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1720 (3 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1720 (3 : Fin 4) = raw2088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1720 raw2088; decide +kernel
    rw [heq]
    exact (canonical2088 hH).trans (sound1066 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1720 + (injectiveMoment H (mergeFirst pivotMatrix1720 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1720 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1720 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1720 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1720, value1041, value1063, value1066, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1721 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1721 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem sound1721 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1721 = Sparse.eval value1721 (momentVector H) := by
  have heq : pivotMatrix1721 = (fun u v => node1721 (pivotPermutation1721 u) v) := by apply Matrix.ext; unfold pivotMatrix1721 node1721 pivotPermutation1721; decide +kernel
  have hmoment : injectiveMoment H node1721 = injectiveMoment H pivotMatrix1721 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1721 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1721 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1721 (0 : Fin 4)) =
      Sparse.eval value1209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1721 (0 : Fin 4) = raw3251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1721 raw3251; decide +kernel
    rw [heq]
    exact (canonical3251 hH).trans (sound1209 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1721 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1721 (1 : Fin 4) = raw2114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1721 raw2114; decide +kernel
    rw [heq]
    exact (canonical2114 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1721 (2 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1721 (2 : Fin 4) = raw2091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1721 raw2091; decide +kernel
    rw [heq]
    exact (canonical2091 hH).trans (sound799 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1721 (3 : Fin 4)) =
      Sparse.eval value492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1721 (3 : Fin 4) = raw2089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1721 raw2089; decide +kernel
    rw [heq]
    exact (canonical2089 hH).trans (sound492 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1721 + (injectiveMoment H (mergeFirst pivotMatrix1721 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1721 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1721 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1721 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1721, value1209, value492, value495, value799, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1722 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1722 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound1722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1722 = Sparse.eval value1722 (momentVector H) := by
  have heq : pivotMatrix1722 = (fun u v => node1722 (pivotPermutation1722 u) v) := by apply Matrix.ext; unfold pivotMatrix1722 node1722 pivotPermutation1722; decide +kernel
  have hmoment : injectiveMoment H node1722 = injectiveMoment H pivotMatrix1722 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1722 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1722 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1722 (0 : Fin 4)) =
      Sparse.eval value934 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1722 (0 : Fin 4) = raw3254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1722 raw3254; decide +kernel
    rw [heq]
    exact (canonical3254 hH).trans (sound934 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1722 (1 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1722 (1 : Fin 4) = raw2116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1722 raw2116; decide +kernel
    rw [heq]
    exact (canonical2116 hH).trans (sound996 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1722 (2 : Fin 4)) =
      Sparse.eval value798 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1722 (2 : Fin 4) = raw2094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1722 raw2094; decide +kernel
    rw [heq]
    exact (canonical2094 hH).trans (sound798 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1722 (3 : Fin 4)) =
      Sparse.eval value493 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1722 (3 : Fin 4) = raw2092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1722 raw2092; decide +kernel
    rw [heq]
    exact (canonical2092 hH).trans (sound493 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1722 + (injectiveMoment H (mergeFirst pivotMatrix1722 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1722 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1722 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1722 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1722, value493, value798, value934, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1723 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1723 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound1723 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1723 = Sparse.eval value1723 (momentVector H) := by
  have heq : pivotMatrix1723 = (fun u v => node1723 (pivotPermutation1723 u) v) := by apply Matrix.ext; unfold pivotMatrix1723 node1723 pivotPermutation1723; decide +kernel
  have hmoment : injectiveMoment H node1723 = injectiveMoment H pivotMatrix1723 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1723 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1723 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1723 (0 : Fin 4)) =
      Sparse.eval value1156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1723 (0 : Fin 4) = raw3255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1723 raw3255; decide +kernel
    rw [heq]
    exact (canonical3255 hH).trans (sound1156 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1723 (1 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1723 (1 : Fin 4) = raw2117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1723 raw2117; decide +kernel
    rw [heq]
    exact (canonical2117 hH).trans (sound1155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1723 (2 : Fin 4)) =
      Sparse.eval value798 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1723 (2 : Fin 4) = raw2095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1723 raw2095; decide +kernel
    rw [heq]
    exact (canonical2095 hH).trans (sound798 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1723 (3 : Fin 4)) =
      Sparse.eval value1106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1723 (3 : Fin 4) = raw2093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1723 raw2093; decide +kernel
    rw [heq]
    exact (canonical2093 hH).trans (sound1106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1723 + (injectiveMoment H (mergeFirst pivotMatrix1723 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1723 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1723 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1723 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1723, value1106, value1155, value1156, value798, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1724 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1724 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem sound1724 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1724 = Sparse.eval value1724 (momentVector H) := by
  have heq : pivotMatrix1724 = (fun u v => node1724 (pivotPermutation1724 u) v) := by apply Matrix.ext; unfold pivotMatrix1724 node1724 pivotPermutation1724; decide +kernel
  have hmoment : injectiveMoment H node1724 = injectiveMoment H pivotMatrix1724 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1724 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1724 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1724 (0 : Fin 4)) =
      Sparse.eval value1281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1724 (0 : Fin 4) = raw3595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1724 raw3595; decide +kernel
    rw [heq]
    exact (canonical3595 hH).trans (sound1281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1724 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1724 (1 : Fin 4) = raw2111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1724 raw2111; decide +kernel
    rw [heq]
    exact (canonical2111 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1724 (2 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1724 (2 : Fin 4) = raw2073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1724 raw2073; decide +kernel
    rw [heq]
    exact (canonical2073 hH).trans (sound816 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1724 (3 : Fin 4)) =
      Sparse.eval value1098 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1724 (3 : Fin 4) = raw2070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1724 raw2070; decide +kernel
    rw [heq]
    exact (canonical2070 hH).trans (sound1098 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1724 + (injectiveMoment H (mergeFirst pivotMatrix1724 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1724 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1724 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1724 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1724, value1098, value1281, value496, value816, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1725 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1725 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem sound1725 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1725 = Sparse.eval value1725 (momentVector H) := by
  have heq : pivotMatrix1725 = (fun u v => node1725 (pivotPermutation1725 u) v) := by apply Matrix.ext; unfold pivotMatrix1725 node1725 pivotPermutation1725; decide +kernel
  have hmoment : injectiveMoment H node1725 = injectiveMoment H pivotMatrix1725 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1725 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1725 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1725 (0 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1725 (0 : Fin 4) = raw3355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1725 raw3355; decide +kernel
    rw [heq]
    exact (canonical3355 hH).trans (sound1037 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1725 (1 : Fin 4)) =
      Sparse.eval value833 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1725 (1 : Fin 4) = raw2210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1725 raw2210; decide +kernel
    rw [heq]
    exact (canonical2210 hH).trans (sound833 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1725 (2 : Fin 4)) =
      Sparse.eval value498 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1725 (2 : Fin 4) = raw2164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1725 raw2164; decide +kernel
    rw [heq]
    exact (canonical2164 hH).trans (sound498 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1725 (3 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1725 (3 : Fin 4) = raw2158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1725 raw2158; decide +kernel
    rw [heq]
    exact (canonical2158 hH).trans (sound1113 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1725 + (injectiveMoment H (mergeFirst pivotMatrix1725 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1725 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1725 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1725 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1725, value1037, value1113, value498, value833, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1726 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1726 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound1726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1726 = Sparse.eval value1726 (momentVector H) := by
  have heq : pivotMatrix1726 = (fun u v => node1726 (pivotPermutation1726 u) v) := by apply Matrix.ext; unfold pivotMatrix1726 node1726 pivotPermutation1726; decide +kernel
  have hmoment : injectiveMoment H node1726 = injectiveMoment H pivotMatrix1726 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1726 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1726 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1726 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1726 (0 : Fin 4) = raw3356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1726 raw3356; decide +kernel
    rw [heq]
    exact (canonical3356 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1726 (1 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1726 (1 : Fin 4) = raw2218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1726 raw2218; decide +kernel
    rw [heq]
    exact (canonical2218 hH).trans (sound831 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1726 (2 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1726 (2 : Fin 4) = raw2168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1726 raw2168; decide +kernel
    rw [heq]
    exact (canonical2168 hH).trans (sound1059 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1726 (3 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1726 (3 : Fin 4) = raw2163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1726 raw2163; decide +kernel
    rw [heq]
    exact (canonical2163 hH).trans (sound497 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1726 + (injectiveMoment H (mergeFirst pivotMatrix1726 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1726 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1726 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1726 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1726, value1027, value1059, value497, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1727 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1727 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound1727 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1727 = Sparse.eval value1727 (momentVector H) := by
  have heq : pivotMatrix1727 = (fun u v => node1727 (pivotPermutation1727 u) v) := by apply Matrix.ext; unfold pivotMatrix1727 node1727 pivotPermutation1727; decide +kernel
  have hmoment : injectiveMoment H node1727 = injectiveMoment H pivotMatrix1727 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1727 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1727 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1727 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1727 (0 : Fin 4) = raw3363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1727 raw3363; decide +kernel
    rw [heq]
    exact (canonical3363 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1727 (1 : Fin 4)) =
      Sparse.eval value826 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1727 (1 : Fin 4) = raw2229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1727 raw2229; decide +kernel
    rw [heq]
    exact (canonical2229 hH).trans (sound826 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1727 (2 : Fin 4)) =
      Sparse.eval value501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1727 (2 : Fin 4) = raw2175 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1727 raw2175; decide +kernel
    rw [heq]
    exact (canonical2175 hH).trans (sound501 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1727 (3 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1727 (3 : Fin 4) = raw2172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1727 raw2172; decide +kernel
    rw [heq]
    exact (canonical2172 hH).trans (sound1100 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1727 + (injectiveMoment H (mergeFirst pivotMatrix1727 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1727 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1727 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1727 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1727, value1100, value501, value771, value826, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
