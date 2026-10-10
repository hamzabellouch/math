import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical49
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical96

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2880 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2880 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2880 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2880 = Sparse.eval value2880 (momentVector H) := by
  have heq : pivotMatrix2880 = (fun u v => node2880 (pivotPermutation2880 u) v) := by apply Matrix.ext; unfold pivotMatrix2880 node2880 pivotPermutation2880; decide +kernel
  have hmoment : injectiveMoment H node2880 = injectiveMoment H pivotMatrix2880 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2880 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2880 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2880 (0 : Fin 5)) =
      Sparse.eval value2403 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2880 (0 : Fin 5) = raw1620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2880 raw1620; decide +kernel
    rw [heq]
    exact (canonical1620 hH).trans (sound2403 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2880 (1 : Fin 5)) =
      Sparse.eval value2596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2880 (1 : Fin 5) = raw1146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2880 raw1146; decide +kernel
    rw [heq]
    exact (canonical1146 hH).trans (sound2596 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2880 (2 : Fin 5)) =
      Sparse.eval value1479 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2880 (2 : Fin 5) = raw1093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2880 raw1093; decide +kernel
    rw [heq]
    exact (canonical1093 hH).trans (sound1479 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2880 (3 : Fin 5)) =
      Sparse.eval value1478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2880 (3 : Fin 5) = raw1087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2880 raw1087; decide +kernel
    rw [heq]
    exact (canonical1087 hH).trans (sound1478 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2880 (4 : Fin 5)) =
      Sparse.eval value1478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2880 (4 : Fin 5) = raw1086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2880 raw1086; decide +kernel
    rw [heq]
    exact (canonical1086 hH).trans (sound1478 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2880 + (injectiveMoment H (mergeFirst pivotMatrix2880 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2880 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2880 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2880 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2880 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2880, value1478, value1479, value2403, value2596, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2881 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2881 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2881 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2881 = Sparse.eval value2881 (momentVector H) := by
  have heq : pivotMatrix2881 = (fun u v => node2881 (pivotPermutation2881 u) v) := by apply Matrix.ext; unfold pivotMatrix2881 node2881 pivotPermutation2881; decide +kernel
  have hmoment : injectiveMoment H node2881 = injectiveMoment H pivotMatrix2881 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2881 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2881 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2881 (0 : Fin 5)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2881 (0 : Fin 5) = raw1626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2881 raw1626; decide +kernel
    rw [heq]
    exact (canonical1626 hH).trans (sound2402 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2881 (1 : Fin 5)) =
      Sparse.eval value2578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2881 (1 : Fin 5) = raw1148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2881 raw1148; decide +kernel
    rw [heq]
    exact (canonical1148 hH).trans (sound2578 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2881 (2 : Fin 5)) =
      Sparse.eval value1476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2881 (2 : Fin 5) = raw1095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2881 raw1095; decide +kernel
    rw [heq]
    exact (canonical1095 hH).trans (sound1476 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2881 (3 : Fin 5)) =
      Sparse.eval value1480 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2881 (3 : Fin 5) = raw1091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2881 raw1091; decide +kernel
    rw [heq]
    exact (canonical1091 hH).trans (sound1480 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2881 (4 : Fin 5)) =
      Sparse.eval value1478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2881 (4 : Fin 5) = raw1090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2881 raw1090; decide +kernel
    rw [heq]
    exact (canonical1090 hH).trans (sound1478 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2881 + (injectiveMoment H (mergeFirst pivotMatrix2881 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2881 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2881 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2881 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2881 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2881, value1476, value1478, value1480, value2402, value2578, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2882 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2882 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound2882 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2882 = Sparse.eval value2882 (momentVector H) := by
  have heq : pivotMatrix2882 = (fun u v => node2882 (pivotPermutation2882 u) v) := by apply Matrix.ext; unfold pivotMatrix2882 node2882 pivotPermutation2882; decide +kernel
  have hmoment : injectiveMoment H node2882 = injectiveMoment H pivotMatrix2882 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2882 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2882 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2882 (0 : Fin 5)) =
      Sparse.eval value1514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2882 (0 : Fin 5) = raw1274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2882 raw1274; decide +kernel
    rw [heq]
    exact (canonical1274 hH).trans (sound1514 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2882 (1 : Fin 5)) =
      Sparse.eval value2786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2882 (1 : Fin 5) = raw1185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2882 raw1185; decide +kernel
    rw [heq]
    exact (canonical1185 hH).trans (sound2786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2882 (2 : Fin 5)) =
      Sparse.eval value1490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2882 (2 : Fin 5) = raw1173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2882 raw1173; decide +kernel
    rw [heq]
    exact (canonical1173 hH).trans (sound1490 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2882 (3 : Fin 5)) =
      Sparse.eval value1490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2882 (3 : Fin 5) = raw1171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2882 raw1171; decide +kernel
    rw [heq]
    exact (canonical1171 hH).trans (sound1490 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2882 (4 : Fin 5)) =
      Sparse.eval value1489 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2882 (4 : Fin 5) = raw1170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2882 raw1170; decide +kernel
    rw [heq]
    exact (canonical1170 hH).trans (sound1489 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2882 + (injectiveMoment H (mergeFirst pivotMatrix2882 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2882 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2882 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2882 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2882 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2882, value1489, value1490, value1514, value2786, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2883 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2883 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

theorem sound2883 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2883 = Sparse.eval value2883 (momentVector H) := by
  have heq : pivotMatrix2883 = (fun u v => node2883 (pivotPermutation2883 u) v) := by apply Matrix.ext; unfold pivotMatrix2883 node2883 pivotPermutation2883; decide +kernel
  have hmoment : injectiveMoment H node2883 = injectiveMoment H pivotMatrix2883 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2883 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2883 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2883 (0 : Fin 5)) =
      Sparse.eval value2736 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2883 (0 : Fin 5) = raw1030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2883 raw1030; decide +kernel
    rw [heq]
    exact (canonical1030 hH).trans (sound2736 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2883 (1 : Fin 5)) =
      Sparse.eval value1488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2883 (1 : Fin 5) = raw1169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2883 raw1169; decide +kernel
    rw [heq]
    exact (canonical1169 hH).trans (sound1488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2883 (2 : Fin 5)) =
      Sparse.eval value1252 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2883 (2 : Fin 5) = raw1178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2883 raw1178; decide +kernel
    rw [heq]
    exact (canonical1178 hH).trans (sound1252 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2883 (3 : Fin 5)) =
      Sparse.eval value1492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2883 (3 : Fin 5) = raw1179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2883 raw1179; decide +kernel
    rw [heq]
    exact (canonical1179 hH).trans (sound1492 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2883 (4 : Fin 5)) =
      Sparse.eval value1493 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2883 (4 : Fin 5) = raw1180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2883 raw1180; decide +kernel
    rw [heq]
    exact (canonical1180 hH).trans (sound1493 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2883 + (injectiveMoment H (mergeFirst pivotMatrix2883 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2883 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2883 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2883 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2883 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2883, value1252, value1488, value1492, value1493, value2736, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2884 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2884 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound2884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2884 = Sparse.eval value2884 (momentVector H) := by
  have heq : pivotMatrix2884 = (fun u v => node2884 (pivotPermutation2884 u) v) := by apply Matrix.ext; unfold pivotMatrix2884 node2884 pivotPermutation2884; decide +kernel
  have hmoment : injectiveMoment H node2884 = injectiveMoment H pivotMatrix2884 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2884 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2884 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2884 (0 : Fin 5)) =
      Sparse.eval value2739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2884 (0 : Fin 5) = raw1053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2884 raw1053; decide +kernel
    rw [heq]
    exact (canonical1053 hH).trans (sound2739 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2884 (1 : Fin 5)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2884 (1 : Fin 5) = raw1200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2884 raw1200; decide +kernel
    rw [heq]
    exact (canonical1200 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2884 (2 : Fin 5)) =
      Sparse.eval value1501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2884 (2 : Fin 5) = raw1204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2884 raw1204; decide +kernel
    rw [heq]
    exact (canonical1204 hH).trans (sound1501 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2884 (3 : Fin 5)) =
      Sparse.eval value1503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2884 (3 : Fin 5) = raw1207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2884 raw1207; decide +kernel
    rw [heq]
    exact (canonical1207 hH).trans (sound1503 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2884 (4 : Fin 5)) =
      Sparse.eval value1504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2884 (4 : Fin 5) = raw1208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2884 raw1208; decide +kernel
    rw [heq]
    exact (canonical1208 hH).trans (sound1504 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2884 + (injectiveMoment H (mergeFirst pivotMatrix2884 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2884 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2884 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2884 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2884 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2884, value1032, value1501, value1503, value1504, value2739, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2885 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2885 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound2885 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2885 = Sparse.eval value2885 (momentVector H) := by
  have heq : pivotMatrix2885 = (fun u v => node2885 (pivotPermutation2885 u) v) := by apply Matrix.ext; unfold pivotMatrix2885 node2885 pivotPermutation2885; decide +kernel
  have hmoment : injectiveMoment H node2885 = injectiveMoment H pivotMatrix2885 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2885 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2885 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2885 (0 : Fin 5)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2885 (0 : Fin 5) = raw1060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2885 raw1060; decide +kernel
    rw [heq]
    exact (canonical1060 hH).trans (sound2749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2885 (1 : Fin 5)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2885 (1 : Fin 5) = raw1202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2885 raw1202; decide +kernel
    rw [heq]
    exact (canonical1202 hH).trans (sound959 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2885 (2 : Fin 5)) =
      Sparse.eval value1504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2885 (2 : Fin 5) = raw1208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2885 raw1208; decide +kernel
    rw [heq]
    exact (canonical1208 hH).trans (sound1504 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2885 (3 : Fin 5)) =
      Sparse.eval value1504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2885 (3 : Fin 5) = raw1212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2885 raw1212; decide +kernel
    rw [heq]
    exact (canonical1212 hH).trans (sound1504 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2885 (4 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2885 (4 : Fin 5) = raw1213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2885 raw1213; decide +kernel
    rw [heq]
    exact (canonical1213 hH).trans (sound1507 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2885 + (injectiveMoment H (mergeFirst pivotMatrix2885 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2885 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2885 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2885 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2885 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2885, value1504, value1507, value2749, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2886 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2886 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2886 = Sparse.eval value2886 (momentVector H) := by
  have heq : pivotMatrix2886 = (fun u v => node2886 (pivotPermutation2886 u) v) := by apply Matrix.ext; unfold pivotMatrix2886 node2886 pivotPermutation2886; decide +kernel
  have hmoment : injectiveMoment H node2886 = injectiveMoment H pivotMatrix2886 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2886 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2886 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2886 (0 : Fin 5)) =
      Sparse.eval value2596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2886 (0 : Fin 5) = raw1123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2886 raw1123; decide +kernel
    rw [heq]
    exact (canonical1123 hH).trans (sound2596 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2886 (1 : Fin 5)) =
      Sparse.eval value1511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2886 (1 : Fin 5) = raw1232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2886 raw1232; decide +kernel
    rw [heq]
    exact (canonical1232 hH).trans (sound1511 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2886 (2 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2886 (2 : Fin 5) = raw1244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2886 raw1244; decide +kernel
    rw [heq]
    exact (canonical1244 hH).trans (sound2823 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2886 (3 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2886 (3 : Fin 5) = raw1246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2886 raw1246; decide +kernel
    rw [heq]
    exact (canonical1246 hH).trans (sound1513 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2886 (4 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2886 (4 : Fin 5) = raw1247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2886 raw1247; decide +kernel
    rw [heq]
    exact (canonical1247 hH).trans (sound1513 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2886 + (injectiveMoment H (mergeFirst pivotMatrix2886 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2886 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2886 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2886 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2886 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2886, value1511, value1513, value2596, value2823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2887 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2887 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2887 = Sparse.eval value2887 (momentVector H) := by
  have heq : pivotMatrix2887 = (fun u v => node2887 (pivotPermutation2887 u) v) := by apply Matrix.ext; unfold pivotMatrix2887 node2887 pivotPermutation2887; decide +kernel
  have hmoment : injectiveMoment H node2887 = injectiveMoment H pivotMatrix2887 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2887 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2887 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2887 (0 : Fin 5)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2887 (0 : Fin 5) = raw1303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2887 raw1303; decide +kernel
    rw [heq]
    exact (canonical1303 hH).trans (sound1523 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2887 (1 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2887 (1 : Fin 5) = raw1244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2887 raw1244; decide +kernel
    rw [heq]
    exact (canonical1244 hH).trans (sound2823 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2887 (2 : Fin 5)) =
      Sparse.eval value1511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2887 (2 : Fin 5) = raw1232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2887 raw1232; decide +kernel
    rw [heq]
    exact (canonical1232 hH).trans (sound1511 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2887 (3 : Fin 5)) =
      Sparse.eval value1510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2887 (3 : Fin 5) = raw1230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2887 raw1230; decide +kernel
    rw [heq]
    exact (canonical1230 hH).trans (sound1510 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2887 (4 : Fin 5)) =
      Sparse.eval value1510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2887 (4 : Fin 5) = raw1229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2887 raw1229; decide +kernel
    rw [heq]
    exact (canonical1229 hH).trans (sound1510 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2887 + (injectiveMoment H (mergeFirst pivotMatrix2887 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2887 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2887 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2887 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2887 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2887, value1510, value1511, value1523, value2823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2888 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2888 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2888 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2888 = Sparse.eval value2888 (momentVector H) := by
  have heq : pivotMatrix2888 = (fun u v => node2888 (pivotPermutation2888 u) v) := by apply Matrix.ext; unfold pivotMatrix2888 node2888 pivotPermutation2888; decide +kernel
  have hmoment : injectiveMoment H node2888 = injectiveMoment H pivotMatrix2888 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2888 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2888 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2888 (0 : Fin 5)) =
      Sparse.eval value1524 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2888 (0 : Fin 5) = raw1308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2888 raw1308; decide +kernel
    rw [heq]
    exact (canonical1308 hH).trans (sound1524 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2888 (1 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2888 (1 : Fin 5) = raw1254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2888 raw1254; decide +kernel
    rw [heq]
    exact (canonical1254 hH).trans (sound2823 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2888 (2 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2888 (2 : Fin 5) = raw1244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2888 raw1244; decide +kernel
    rw [heq]
    exact (canonical1244 hH).trans (sound2823 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2888 (3 : Fin 5)) =
      Sparse.eval value1512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2888 (3 : Fin 5) = raw1241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2888 raw1241; decide +kernel
    rw [heq]
    exact (canonical1241 hH).trans (sound1512 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2888 (4 : Fin 5)) =
      Sparse.eval value1512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2888 (4 : Fin 5) = raw1240 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2888 raw1240; decide +kernel
    rw [heq]
    exact (canonical1240 hH).trans (sound1512 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2888 + (injectiveMoment H (mergeFirst pivotMatrix2888 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2888 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2888 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2888 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2888 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2888, value1512, value1524, value2823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2889 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2889 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2889 = Sparse.eval value2889 (momentVector H) := by
  have heq : pivotMatrix2889 = (fun u v => node2889 (pivotPermutation2889 u) v) := by apply Matrix.ext; unfold pivotMatrix2889 node2889 pivotPermutation2889; decide +kernel
  have hmoment : injectiveMoment H node2889 = injectiveMoment H pivotMatrix2889 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2889 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2889 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2889 (0 : Fin 5)) =
      Sparse.eval value1525 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2889 (0 : Fin 5) = raw1310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2889 raw1310; decide +kernel
    rw [heq]
    exact (canonical1310 hH).trans (sound1525 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2889 (1 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2889 (1 : Fin 5) = raw1256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2889 raw1256; decide +kernel
    rw [heq]
    exact (canonical1256 hH).trans (sound2823 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2889 (2 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2889 (2 : Fin 5) = raw1246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2889 raw1246; decide +kernel
    rw [heq]
    exact (canonical1246 hH).trans (sound1513 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2889 (3 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2889 (3 : Fin 5) = raw1244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2889 raw1244; decide +kernel
    rw [heq]
    exact (canonical1244 hH).trans (sound2823 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2889 (4 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2889 (4 : Fin 5) = raw1243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2889 raw1243; decide +kernel
    rw [heq]
    exact (canonical1243 hH).trans (sound1513 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2889 + (injectiveMoment H (mergeFirst pivotMatrix2889 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2889 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2889 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2889 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2889 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2889, value1513, value1525, value2823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2890 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2890 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound2890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2890 = Sparse.eval value2890 (momentVector H) := by
  have heq : pivotMatrix2890 = (fun u v => node2890 (pivotPermutation2890 u) v) := by apply Matrix.ext; unfold pivotMatrix2890 node2890 pivotPermutation2890; decide +kernel
  have hmoment : injectiveMoment H node2890 = injectiveMoment H pivotMatrix2890 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2890 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2890 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2890 (0 : Fin 5)) =
      Sparse.eval value1509 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2890 (0 : Fin 5) = raw1334 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2890 raw1334; decide +kernel
    rw [heq]
    exact (canonical1334 hH).trans (sound1509 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2890 (1 : Fin 5)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2890 (1 : Fin 5) = raw1289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2890 raw1289; decide +kernel
    rw [heq]
    exact (canonical1289 hH).trans (sound1521 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2890 (2 : Fin 5)) =
      Sparse.eval value1515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2890 (2 : Fin 5) = raw1279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2890 raw1279; decide +kernel
    rw [heq]
    exact (canonical1279 hH).trans (sound1515 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2890 (3 : Fin 5)) =
      Sparse.eval value1515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2890 (3 : Fin 5) = raw1275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2890 raw1275; decide +kernel
    rw [heq]
    exact (canonical1275 hH).trans (sound1515 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2890 (4 : Fin 5)) =
      Sparse.eval value1514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2890 (4 : Fin 5) = raw1274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2890 raw1274; decide +kernel
    rw [heq]
    exact (canonical1274 hH).trans (sound1514 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2890 + (injectiveMoment H (mergeFirst pivotMatrix2890 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2890 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2890 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2890 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2890 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2890, value1509, value1514, value1515, value1521, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2891 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2891 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2891 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2891 = Sparse.eval value2891 (momentVector H) := by
  have heq : pivotMatrix2891 = (fun u v => node2891 (pivotPermutation2891 u) v) := by apply Matrix.ext; unfold pivotMatrix2891 node2891 pivotPermutation2891; decide +kernel
  have hmoment : injectiveMoment H node2891 = injectiveMoment H pivotMatrix2891 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2891 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2891 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2891 (0 : Fin 5)) =
      Sparse.eval value2453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2891 (0 : Fin 5) = raw2554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2891 raw2554; decide +kernel
    rw [heq]
    exact (canonical2554 hH).trans (sound2453 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2891 (1 : Fin 5)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2891 (1 : Fin 5) = raw1303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2891 raw1303; decide +kernel
    rw [heq]
    exact (canonical1303 hH).trans (sound1523 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2891 (2 : Fin 5)) =
      Sparse.eval value1514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2891 (2 : Fin 5) = raw1281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2891 raw1281; decide +kernel
    rw [heq]
    exact (canonical1281 hH).trans (sound1514 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2891 (3 : Fin 5)) =
      Sparse.eval value1516 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2891 (3 : Fin 5) = raw1277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2891 raw1277; decide +kernel
    rw [heq]
    exact (canonical1277 hH).trans (sound1516 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2891 (4 : Fin 5)) =
      Sparse.eval value1516 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2891 (4 : Fin 5) = raw1276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2891 raw1276; decide +kernel
    rw [heq]
    exact (canonical1276 hH).trans (sound1516 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2891 + (injectiveMoment H (mergeFirst pivotMatrix2891 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2891 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2891 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2891 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2891 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2891, value1514, value1516, value1523, value2453, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2892 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2892 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound2892 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2892 = Sparse.eval value2892 (momentVector H) := by
  have heq : pivotMatrix2892 = (fun u v => node2892 (pivotPermutation2892 u) v) := by apply Matrix.ext; unfold pivotMatrix2892 node2892 pivotPermutation2892; decide +kernel
  have hmoment : injectiveMoment H node2892 = injectiveMoment H pivotMatrix2892 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2892 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2892 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2892 (0 : Fin 5)) =
      Sparse.eval value1503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2892 (0 : Fin 5) = raw1207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2892 raw1207; decide +kernel
    rw [heq]
    exact (canonical1207 hH).trans (sound1503 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2892 (1 : Fin 5)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2892 (1 : Fin 5) = raw1296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2892 raw1296; decide +kernel
    rw [heq]
    exact (canonical1296 hH).trans (sound1027 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2892 (2 : Fin 5)) =
      Sparse.eval value1522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2892 (2 : Fin 5) = raw1298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2892 raw1298; decide +kernel
    rw [heq]
    exact (canonical1298 hH).trans (sound1522 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2892 (3 : Fin 5)) =
      Sparse.eval value1522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2892 (3 : Fin 5) = raw1300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2892 raw1300; decide +kernel
    rw [heq]
    exact (canonical1300 hH).trans (sound1522 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2892 (4 : Fin 5)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2892 (4 : Fin 5) = raw1301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2892 raw1301; decide +kernel
    rw [heq]
    exact (canonical1301 hH).trans (sound1521 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2892 + (injectiveMoment H (mergeFirst pivotMatrix2892 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2892 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2892 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2892 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2892 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2892, value1027, value1503, value1521, value1522, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2893 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2893 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound2893 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2893 = Sparse.eval value2893 (momentVector H) := by
  have heq : pivotMatrix2893 = (fun u v => node2893 (pivotPermutation2893 u) v) := by apply Matrix.ext; unfold pivotMatrix2893 node2893 pivotPermutation2893; decide +kernel
  have hmoment : injectiveMoment H node2893 = injectiveMoment H pivotMatrix2893 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2893 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2893 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2893 (0 : Fin 5)) =
      Sparse.eval value1504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2893 (0 : Fin 5) = raw1208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2893 raw1208; decide +kernel
    rw [heq]
    exact (canonical1208 hH).trans (sound1504 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2893 (1 : Fin 5)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2893 (1 : Fin 5) = raw1297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2893 raw1297; decide +kernel
    rw [heq]
    exact (canonical1297 hH).trans (sound1033 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2893 (2 : Fin 5)) =
      Sparse.eval value1519 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2893 (2 : Fin 5) = raw1299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2893 raw1299; decide +kernel
    rw [heq]
    exact (canonical1299 hH).trans (sound1519 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2893 (3 : Fin 5)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2893 (3 : Fin 5) = raw1301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2893 raw1301; decide +kernel
    rw [heq]
    exact (canonical1301 hH).trans (sound1521 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2893 (4 : Fin 5)) =
      Sparse.eval value1518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2893 (4 : Fin 5) = raw1302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2893 raw1302; decide +kernel
    rw [heq]
    exact (canonical1302 hH).trans (sound1518 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2893 + (injectiveMoment H (mergeFirst pivotMatrix2893 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2893 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2893 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2893 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2893 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2893, value1033, value1504, value1518, value1519, value1521, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2894 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2894 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2894 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2894 = Sparse.eval value2894 (momentVector H) := by
  have heq : pivotMatrix2894 = (fun u v => node2894 (pivotPermutation2894 u) v) := by apply Matrix.ext; unfold pivotMatrix2894 node2894 pivotPermutation2894; decide +kernel
  have hmoment : injectiveMoment H node2894 = injectiveMoment H pivotMatrix2894 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2894 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2894 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2894 (0 : Fin 5)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2894 (0 : Fin 5) = raw1244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2894 raw1244; decide +kernel
    rw [heq]
    exact (canonical1244 hH).trans (sound2823 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2894 (1 : Fin 5)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2894 (1 : Fin 5) = raw1303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2894 raw1303; decide +kernel
    rw [heq]
    exact (canonical1303 hH).trans (sound1523 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2894 (2 : Fin 5)) =
      Sparse.eval value1524 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2894 (2 : Fin 5) = raw1308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2894 raw1308; decide +kernel
    rw [heq]
    exact (canonical1308 hH).trans (sound1524 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2894 (3 : Fin 5)) =
      Sparse.eval value1525 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2894 (3 : Fin 5) = raw1310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2894 raw1310; decide +kernel
    rw [heq]
    exact (canonical1310 hH).trans (sound1525 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2894 (4 : Fin 5)) =
      Sparse.eval value1525 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2894 (4 : Fin 5) = raw1311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2894 raw1311; decide +kernel
    rw [heq]
    exact (canonical1311 hH).trans (sound1525 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2894 + (injectiveMoment H (mergeFirst pivotMatrix2894 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2894 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2894 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2894 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2894 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2894, value1523, value1524, value1525, value2823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2895 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2895 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem sound2895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2895 = Sparse.eval value2895 (momentVector H) := by
  have heq : pivotMatrix2895 = (fun u v => node2895 (pivotPermutation2895 u) v) := by apply Matrix.ext; unfold pivotMatrix2895 node2895 pivotPermutation2895; decide +kernel
  have hmoment : injectiveMoment H node2895 = injectiveMoment H pivotMatrix2895 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2895 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2895 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2895 (0 : Fin 5)) =
      Sparse.eval value1440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2895 (0 : Fin 5) = raw967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2895 raw967; decide +kernel
    rw [heq]
    exact (canonical967 hH).trans (sound1440 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2895 (1 : Fin 5)) =
      Sparse.eval value1548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2895 (1 : Fin 5) = raw1461 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2895 raw1461; decide +kernel
    rw [heq]
    exact (canonical1461 hH).trans (sound1548 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2895 (2 : Fin 5)) =
      Sparse.eval value1548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2895 (2 : Fin 5) = raw1529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2895 raw1529; decide +kernel
    rw [heq]
    exact (canonical1529 hH).trans (sound1548 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2895 (3 : Fin 5)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2895 (3 : Fin 5) = raw1543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2895 raw1543; decide +kernel
    rw [heq]
    exact (canonical1543 hH).trans (sound907 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2895 (4 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2895 (4 : Fin 5) = raw1546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2895 raw1546; decide +kernel
    rw [heq]
    exact (canonical1546 hH).trans (sound2394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2895 + (injectiveMoment H (mergeFirst pivotMatrix2895 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2895 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2895 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2895 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2895 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2895, value1440, value1548, value2394, value907, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2896 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2896 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem sound2896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2896 = Sparse.eval value2896 (momentVector H) := by
  have heq : pivotMatrix2896 = (fun u v => node2896 (pivotPermutation2896 u) v) := by apply Matrix.ext; unfold pivotMatrix2896 node2896 pivotPermutation2896; decide +kernel
  have hmoment : injectiveMoment H node2896 = injectiveMoment H pivotMatrix2896 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2896 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2896 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2896 (0 : Fin 5)) =
      Sparse.eval value1439 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2896 (0 : Fin 5) = raw968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2896 raw968; decide +kernel
    rw [heq]
    exact (canonical968 hH).trans (sound1439 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2896 (1 : Fin 5)) =
      Sparse.eval value1551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2896 (1 : Fin 5) = raw1464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2896 raw1464; decide +kernel
    rw [heq]
    exact (canonical1464 hH).trans (sound1551 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2896 (2 : Fin 5)) =
      Sparse.eval value1551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2896 (2 : Fin 5) = raw1530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2896 raw1530; decide +kernel
    rw [heq]
    exact (canonical1530 hH).trans (sound1551 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2896 (3 : Fin 5)) =
      Sparse.eval value1584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2896 (3 : Fin 5) = raw1551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2896 raw1551; decide +kernel
    rw [heq]
    exact (canonical1551 hH).trans (sound1584 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2896 (4 : Fin 5)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2896 (4 : Fin 5) = raw1554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2896 raw1554; decide +kernel
    rw [heq]
    exact (canonical1554 hH).trans (sound2390 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2896 + (injectiveMoment H (mergeFirst pivotMatrix2896 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2896 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2896 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2896 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2896 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2896, value1439, value1551, value1584, value2390, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2897 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2897 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem sound2897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2897 = Sparse.eval value2897 (momentVector H) := by
  have heq : pivotMatrix2897 = (fun u v => node2897 (pivotPermutation2897 u) v) := by apply Matrix.ext; unfold pivotMatrix2897 node2897 pivotPermutation2897; decide +kernel
  have hmoment : injectiveMoment H node2897 = injectiveMoment H pivotMatrix2897 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2897 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2897 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2897 (0 : Fin 5)) =
      Sparse.eval value1440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2897 (0 : Fin 5) = raw969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2897 raw969; decide +kernel
    rw [heq]
    exact (canonical969 hH).trans (sound1440 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2897 (1 : Fin 5)) =
      Sparse.eval value1552 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2897 (1 : Fin 5) = raw1465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2897 raw1465; decide +kernel
    rw [heq]
    exact (canonical1465 hH).trans (sound1552 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2897 (2 : Fin 5)) =
      Sparse.eval value1552 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2897 (2 : Fin 5) = raw1531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2897 raw1531; decide +kernel
    rw [heq]
    exact (canonical1531 hH).trans (sound1552 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2897 (3 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2897 (3 : Fin 5) = raw1552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2897 raw1552; decide +kernel
    rw [heq]
    exact (canonical1552 hH).trans (sound1585 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2897 (4 : Fin 5)) =
      Sparse.eval value2391 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2897 (4 : Fin 5) = raw1555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2897 raw1555; decide +kernel
    rw [heq]
    exact (canonical1555 hH).trans (sound2391 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2897 + (injectiveMoment H (mergeFirst pivotMatrix2897 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2897 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2897 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2897 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2897 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2897, value1440, value1552, value1585, value2391, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2898 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2898 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2898 = Sparse.eval value2898 (momentVector H) := by
  have heq : pivotMatrix2898 = (fun u v => node2898 (pivotPermutation2898 u) v) := by apply Matrix.ext; unfold pivotMatrix2898 node2898 pivotPermutation2898; decide +kernel
  have hmoment : injectiveMoment H node2898 = injectiveMoment H pivotMatrix2898 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2898 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2898 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2898 (0 : Fin 5)) =
      Sparse.eval value1441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2898 (0 : Fin 5) = raw981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2898 raw981; decide +kernel
    rw [heq]
    exact (canonical981 hH).trans (sound1441 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2898 (1 : Fin 5)) =
      Sparse.eval value1563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2898 (1 : Fin 5) = raw1474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2898 raw1474; decide +kernel
    rw [heq]
    exact (canonical1474 hH).trans (sound1563 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2898 (2 : Fin 5)) =
      Sparse.eval value2399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2898 (2 : Fin 5) = raw1586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2898 raw1586; decide +kernel
    rw [heq]
    exact (canonical1586 hH).trans (sound2399 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2898 (3 : Fin 5)) =
      Sparse.eval value1604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2898 (3 : Fin 5) = raw1605 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2898 raw1605; decide +kernel
    rw [heq]
    exact (canonical1605 hH).trans (sound1604 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2898 (4 : Fin 5)) =
      Sparse.eval value1605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2898 (4 : Fin 5) = raw1607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2898 raw1607; decide +kernel
    rw [heq]
    exact (canonical1607 hH).trans (sound1605 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2898 + (injectiveMoment H (mergeFirst pivotMatrix2898 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2898 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2898 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2898 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2898 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2898, value1441, value1563, value1604, value1605, value2399, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2899 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2899 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem sound2899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2899 = Sparse.eval value2899 (momentVector H) := by
  have heq : pivotMatrix2899 = (fun u v => node2899 (pivotPermutation2899 u) v) := by apply Matrix.ext; unfold pivotMatrix2899 node2899 pivotPermutation2899; decide +kernel
  have hmoment : injectiveMoment H node2899 = injectiveMoment H pivotMatrix2899 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2899 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2899 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2899 (0 : Fin 5)) =
      Sparse.eval value1453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2899 (0 : Fin 5) = raw1006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2899 raw1006; decide +kernel
    rw [heq]
    exact (canonical1006 hH).trans (sound1453 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2899 (1 : Fin 5)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2899 (1 : Fin 5) = raw1524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2899 raw1524; decide +kernel
    rw [heq]
    exact (canonical1524 hH).trans (sound1171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2899 (2 : Fin 5)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2899 (2 : Fin 5) = raw1670 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2899 raw1670; decide +kernel
    rw [heq]
    exact (canonical1670 hH).trans (sound1171 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2899 (3 : Fin 5)) =
      Sparse.eval value1584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2899 (3 : Fin 5) = raw1676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2899 raw1676; decide +kernel
    rw [heq]
    exact (canonical1676 hH).trans (sound1584 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2899 (4 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2899 (4 : Fin 5) = raw1679 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2899 raw1679; decide +kernel
    rw [heq]
    exact (canonical1679 hH).trans (sound1585 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2899 + (injectiveMoment H (mergeFirst pivotMatrix2899 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2899 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2899 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2899 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2899 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2899, value1171, value1453, value1584, value1585, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2900 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2900 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem sound2900 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2900 = Sparse.eval value2900 (momentVector H) := by
  have heq : pivotMatrix2900 = (fun u v => node2900 (pivotPermutation2900 u) v) := by apply Matrix.ext; unfold pivotMatrix2900 node2900 pivotPermutation2900; decide +kernel
  have hmoment : injectiveMoment H node2900 = injectiveMoment H pivotMatrix2900 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2900 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2900 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2900 (0 : Fin 5)) =
      Sparse.eval value1458 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2900 (0 : Fin 5) = raw1039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2900 raw1039; decide +kernel
    rw [heq]
    exact (canonical1039 hH).trans (sound1458 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2900 (1 : Fin 5)) =
      Sparse.eval value1564 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2900 (1 : Fin 5) = raw1475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2900 raw1475; decide +kernel
    rw [heq]
    exact (canonical1475 hH).trans (sound1564 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2900 (2 : Fin 5)) =
      Sparse.eval value1564 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2900 (2 : Fin 5) = raw1532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2900 raw1532; decide +kernel
    rw [heq]
    exact (canonical1532 hH).trans (sound1564 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2900 (3 : Fin 5)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2900 (3 : Fin 5) = raw1543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2900 raw1543; decide +kernel
    rw [heq]
    exact (canonical1543 hH).trans (sound907 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2900 (4 : Fin 5)) =
      Sparse.eval value2395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2900 (4 : Fin 5) = raw1545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2900 raw1545; decide +kernel
    rw [heq]
    exact (canonical1545 hH).trans (sound2395 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2900 + (injectiveMoment H (mergeFirst pivotMatrix2900 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2900 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2900 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2900 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2900 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2900, value1458, value1564, value2395, value907, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2901 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2901 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem sound2901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2901 = Sparse.eval value2901 (momentVector H) := by
  have heq : pivotMatrix2901 = (fun u v => node2901 (pivotPermutation2901 u) v) := by apply Matrix.ext; unfold pivotMatrix2901 node2901 pivotPermutation2901; decide +kernel
  have hmoment : injectiveMoment H node2901 = injectiveMoment H pivotMatrix2901 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2901 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2901 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2901 (0 : Fin 5)) =
      Sparse.eval value1459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2901 (0 : Fin 5) = raw1040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2901 raw1040; decide +kernel
    rw [heq]
    exact (canonical1040 hH).trans (sound1459 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2901 (1 : Fin 5)) =
      Sparse.eval value1565 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2901 (1 : Fin 5) = raw1476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2901 raw1476; decide +kernel
    rw [heq]
    exact (canonical1476 hH).trans (sound1565 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2901 (2 : Fin 5)) =
      Sparse.eval value1565 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2901 (2 : Fin 5) = raw1533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2901 raw1533; decide +kernel
    rw [heq]
    exact (canonical1533 hH).trans (sound1565 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2901 (3 : Fin 5)) =
      Sparse.eval value2389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2901 (3 : Fin 5) = raw1544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2901 raw1544; decide +kernel
    rw [heq]
    exact (canonical1544 hH).trans (sound2389 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2901 (4 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2901 (4 : Fin 5) = raw1546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2901 raw1546; decide +kernel
    rw [heq]
    exact (canonical1546 hH).trans (sound2394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2901 + (injectiveMoment H (mergeFirst pivotMatrix2901 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2901 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2901 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2901 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2901 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2901, value1459, value1565, value2389, value2394, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2902 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2902 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem sound2902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2902 = Sparse.eval value2902 (momentVector H) := by
  have heq : pivotMatrix2902 = (fun u v => node2902 (pivotPermutation2902 u) v) := by apply Matrix.ext; unfold pivotMatrix2902 node2902 pivotPermutation2902; decide +kernel
  have hmoment : injectiveMoment H node2902 = injectiveMoment H pivotMatrix2902 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2902 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2902 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2902 (0 : Fin 5)) =
      Sparse.eval value1460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2902 (0 : Fin 5) = raw1041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2902 raw1041; decide +kernel
    rw [heq]
    exact (canonical1041 hH).trans (sound1460 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2902 (1 : Fin 5)) =
      Sparse.eval value1566 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2902 (1 : Fin 5) = raw1477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2902 raw1477; decide +kernel
    rw [heq]
    exact (canonical1477 hH).trans (sound1566 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2902 (2 : Fin 5)) =
      Sparse.eval value1566 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2902 (2 : Fin 5) = raw1534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2902 raw1534; decide +kernel
    rw [heq]
    exact (canonical1534 hH).trans (sound1566 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2902 (3 : Fin 5)) =
      Sparse.eval value2395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2902 (3 : Fin 5) = raw1545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2902 raw1545; decide +kernel
    rw [heq]
    exact (canonical1545 hH).trans (sound2395 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2902 (4 : Fin 5)) =
      Sparse.eval value1582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2902 (4 : Fin 5) = raw1548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2902 raw1548; decide +kernel
    rw [heq]
    exact (canonical1548 hH).trans (sound1582 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2902 + (injectiveMoment H (mergeFirst pivotMatrix2902 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2902 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2902 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2902 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2902 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2902, value1460, value1566, value1582, value2395, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2903 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2903 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem sound2903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2903 = Sparse.eval value2903 (momentVector H) := by
  have heq : pivotMatrix2903 = (fun u v => node2903 (pivotPermutation2903 u) v) := by apply Matrix.ext; unfold pivotMatrix2903 node2903 pivotPermutation2903; decide +kernel
  have hmoment : injectiveMoment H node2903 = injectiveMoment H pivotMatrix2903 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2903 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2903 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2903 (0 : Fin 5)) =
      Sparse.eval value1461 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2903 (0 : Fin 5) = raw1042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2903 raw1042; decide +kernel
    rw [heq]
    exact (canonical1042 hH).trans (sound1461 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2903 (1 : Fin 5)) =
      Sparse.eval value1567 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2903 (1 : Fin 5) = raw1478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2903 raw1478; decide +kernel
    rw [heq]
    exact (canonical1478 hH).trans (sound1567 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2903 (2 : Fin 5)) =
      Sparse.eval value1567 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2903 (2 : Fin 5) = raw1535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2903 raw1535; decide +kernel
    rw [heq]
    exact (canonical1535 hH).trans (sound1567 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2903 (3 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2903 (3 : Fin 5) = raw1546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2903 raw1546; decide +kernel
    rw [heq]
    exact (canonical1546 hH).trans (sound2394 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2903 (4 : Fin 5)) =
      Sparse.eval value1573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2903 (4 : Fin 5) = raw1549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2903 raw1549; decide +kernel
    rw [heq]
    exact (canonical1549 hH).trans (sound1573 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2903 + (injectiveMoment H (mergeFirst pivotMatrix2903 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2903 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2903 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2903 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2903 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2903, value1461, value1567, value1573, value2394, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2904 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2904 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem sound2904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2904 = Sparse.eval value2904 (momentVector H) := by
  have heq : pivotMatrix2904 = (fun u v => node2904 (pivotPermutation2904 u) v) := by apply Matrix.ext; unfold pivotMatrix2904 node2904 pivotPermutation2904; decide +kernel
  have hmoment : injectiveMoment H node2904 = injectiveMoment H pivotMatrix2904 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2904 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2904 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2904 (0 : Fin 5)) =
      Sparse.eval value1460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2904 (0 : Fin 5) = raw1043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2904 raw1043; decide +kernel
    rw [heq]
    exact (canonical1043 hH).trans (sound1460 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2904 (1 : Fin 5)) =
      Sparse.eval value1568 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2904 (1 : Fin 5) = raw1479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2904 raw1479; decide +kernel
    rw [heq]
    exact (canonical1479 hH).trans (sound1568 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2904 (2 : Fin 5)) =
      Sparse.eval value1568 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2904 (2 : Fin 5) = raw1536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2904 raw1536; decide +kernel
    rw [heq]
    exact (canonical1536 hH).trans (sound1568 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2904 (3 : Fin 5)) =
      Sparse.eval value2393 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2904 (3 : Fin 5) = raw1547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2904 raw1547; decide +kernel
    rw [heq]
    exact (canonical1547 hH).trans (sound2393 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2904 (4 : Fin 5)) =
      Sparse.eval value1583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2904 (4 : Fin 5) = raw1550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2904 raw1550; decide +kernel
    rw [heq]
    exact (canonical1550 hH).trans (sound1583 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2904 + (injectiveMoment H (mergeFirst pivotMatrix2904 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2904 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2904 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2904 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2904 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2904, value1460, value1568, value1583, value2393, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2905 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2905 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem sound2905 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2905 = Sparse.eval value2905 (momentVector H) := by
  have heq : pivotMatrix2905 = (fun u v => node2905 (pivotPermutation2905 u) v) := by apply Matrix.ext; unfold pivotMatrix2905 node2905 pivotPermutation2905; decide +kernel
  have hmoment : injectiveMoment H node2905 = injectiveMoment H pivotMatrix2905 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2905 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2905 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2905 (0 : Fin 5)) =
      Sparse.eval value1458 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2905 (0 : Fin 5) = raw1044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2905 raw1044; decide +kernel
    rw [heq]
    exact (canonical1044 hH).trans (sound1458 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2905 (1 : Fin 5)) =
      Sparse.eval value1569 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2905 (1 : Fin 5) = raw1480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2905 raw1480; decide +kernel
    rw [heq]
    exact (canonical1480 hH).trans (sound1569 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2905 (2 : Fin 5)) =
      Sparse.eval value1569 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2905 (2 : Fin 5) = raw1537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2905 raw1537; decide +kernel
    rw [heq]
    exact (canonical1537 hH).trans (sound1569 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2905 (3 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2905 (3 : Fin 5) = raw1552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2905 raw1552; decide +kernel
    rw [heq]
    exact (canonical1552 hH).trans (sound1585 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2905 (4 : Fin 5)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2905 (4 : Fin 5) = raw1554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2905 raw1554; decide +kernel
    rw [heq]
    exact (canonical1554 hH).trans (sound2390 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2905 + (injectiveMoment H (mergeFirst pivotMatrix2905 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2905 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2905 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2905 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2905 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2905, value1458, value1569, value1585, value2390, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2906 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2906 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem sound2906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2906 = Sparse.eval value2906 (momentVector H) := by
  have heq : pivotMatrix2906 = (fun u v => node2906 (pivotPermutation2906 u) v) := by apply Matrix.ext; unfold pivotMatrix2906 node2906 pivotPermutation2906; decide +kernel
  have hmoment : injectiveMoment H node2906 = injectiveMoment H pivotMatrix2906 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2906 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2906 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2906 (0 : Fin 5)) =
      Sparse.eval value1459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2906 (0 : Fin 5) = raw1045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2906 raw1045; decide +kernel
    rw [heq]
    exact (canonical1045 hH).trans (sound1459 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2906 (1 : Fin 5)) =
      Sparse.eval value1570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2906 (1 : Fin 5) = raw1481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2906 raw1481; decide +kernel
    rw [heq]
    exact (canonical1481 hH).trans (sound1570 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2906 (2 : Fin 5)) =
      Sparse.eval value1570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2906 (2 : Fin 5) = raw1538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2906 raw1538; decide +kernel
    rw [heq]
    exact (canonical1538 hH).trans (sound1570 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2906 (3 : Fin 5)) =
      Sparse.eval value1586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2906 (3 : Fin 5) = raw1553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2906 raw1553; decide +kernel
    rw [heq]
    exact (canonical1553 hH).trans (sound1586 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2906 (4 : Fin 5)) =
      Sparse.eval value2391 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2906 (4 : Fin 5) = raw1555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2906 raw1555; decide +kernel
    rw [heq]
    exact (canonical1555 hH).trans (sound2391 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2906 + (injectiveMoment H (mergeFirst pivotMatrix2906 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2906 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2906 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2906 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2906 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2906, value1459, value1570, value1586, value2391, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2907 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2907 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem sound2907 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2907 = Sparse.eval value2907 (momentVector H) := by
  have heq : pivotMatrix2907 = (fun u v => node2907 (pivotPermutation2907 u) v) := by apply Matrix.ext; unfold pivotMatrix2907 node2907 pivotPermutation2907; decide +kernel
  have hmoment : injectiveMoment H node2907 = injectiveMoment H pivotMatrix2907 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2907 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2907 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2907 (0 : Fin 5)) =
      Sparse.eval value1462 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2907 (0 : Fin 5) = raw1046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2907 raw1046; decide +kernel
    rw [heq]
    exact (canonical1046 hH).trans (sound1462 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2907 (1 : Fin 5)) =
      Sparse.eval value1571 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2907 (1 : Fin 5) = raw1482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2907 raw1482; decide +kernel
    rw [heq]
    exact (canonical1482 hH).trans (sound1571 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2907 (2 : Fin 5)) =
      Sparse.eval value1571 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2907 (2 : Fin 5) = raw1539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2907 raw1539; decide +kernel
    rw [heq]
    exact (canonical1539 hH).trans (sound1571 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2907 (3 : Fin 5)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2907 (3 : Fin 5) = raw1554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2907 raw1554; decide +kernel
    rw [heq]
    exact (canonical1554 hH).trans (sound2390 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2907 (4 : Fin 5)) =
      Sparse.eval value2392 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2907 (4 : Fin 5) = raw1557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2907 raw1557; decide +kernel
    rw [heq]
    exact (canonical1557 hH).trans (sound2392 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2907 + (injectiveMoment H (mergeFirst pivotMatrix2907 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2907 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2907 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2907 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2907 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2907, value1462, value1571, value2390, value2392, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2908 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2908 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound2908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2908 = Sparse.eval value2908 (momentVector H) := by
  have heq : pivotMatrix2908 = (fun u v => node2908 (pivotPermutation2908 u) v) := by apply Matrix.ext; unfold pivotMatrix2908 node2908 pivotPermutation2908; decide +kernel
  have hmoment : injectiveMoment H node2908 = injectiveMoment H pivotMatrix2908 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2908 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2908 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2908 (0 : Fin 5)) =
      Sparse.eval value2739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2908 (0 : Fin 5) = raw1053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2908 raw1053; decide +kernel
    rw [heq]
    exact (canonical1053 hH).trans (sound2739 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2908 (1 : Fin 5)) =
      Sparse.eval value1549 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2908 (1 : Fin 5) = raw1483 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2908 raw1483; decide +kernel
    rw [heq]
    exact (canonical1483 hH).trans (sound1549 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2908 (2 : Fin 5)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2908 (2 : Fin 5) = raw1540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2908 raw1540; decide +kernel
    rw [heq]
    exact (canonical1540 hH).trans (sound915 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2908 (3 : Fin 5)) =
      Sparse.eval value2395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2908 (3 : Fin 5) = raw1561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2908 raw1561; decide +kernel
    rw [heq]
    exact (canonical1561 hH).trans (sound2395 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2908 (4 : Fin 5)) =
      Sparse.eval value1548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2908 (4 : Fin 5) = raw1564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2908 raw1564; decide +kernel
    rw [heq]
    exact (canonical1564 hH).trans (sound1548 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2908 + (injectiveMoment H (mergeFirst pivotMatrix2908 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2908 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2908 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2908 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2908 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2908, value1548, value1549, value2395, value2739, value915, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2909 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2909 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound2909 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2909 = Sparse.eval value2909 (momentVector H) := by
  have heq : pivotMatrix2909 = (fun u v => node2909 (pivotPermutation2909 u) v) := by apply Matrix.ext; unfold pivotMatrix2909 node2909 pivotPermutation2909; decide +kernel
  have hmoment : injectiveMoment H node2909 = injectiveMoment H pivotMatrix2909 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2909 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2909 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2909 (0 : Fin 5)) =
      Sparse.eval value1468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2909 (0 : Fin 5) = raw1054 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2909 raw1054; decide +kernel
    rw [heq]
    exact (canonical1054 hH).trans (sound1468 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2909 (1 : Fin 5)) =
      Sparse.eval value1572 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2909 (1 : Fin 5) = raw1484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2909 raw1484; decide +kernel
    rw [heq]
    exact (canonical1484 hH).trans (sound1572 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2909 (2 : Fin 5)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2909 (2 : Fin 5) = raw1541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2909 raw1541; decide +kernel
    rw [heq]
    exact (canonical1541 hH).trans (sound769 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2909 (3 : Fin 5)) =
      Sparse.eval value2398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2909 (3 : Fin 5) = raw1562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2909 raw1562; decide +kernel
    rw [heq]
    exact (canonical1562 hH).trans (sound2398 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2909 (4 : Fin 5)) =
      Sparse.eval value1557 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2909 (4 : Fin 5) = raw1565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2909 raw1565; decide +kernel
    rw [heq]
    exact (canonical1565 hH).trans (sound1557 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2909 + (injectiveMoment H (mergeFirst pivotMatrix2909 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2909 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2909 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2909 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2909 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2909, value1468, value1557, value1572, value2398, value769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2910 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2910 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound2910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2910 = Sparse.eval value2910 (momentVector H) := by
  have heq : pivotMatrix2910 = (fun u v => node2910 (pivotPermutation2910 u) v) := by apply Matrix.ext; unfold pivotMatrix2910 node2910 pivotPermutation2910; decide +kernel
  have hmoment : injectiveMoment H node2910 = injectiveMoment H pivotMatrix2910 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2910 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2910 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2910 (0 : Fin 5)) =
      Sparse.eval value2747 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2910 (0 : Fin 5) = raw1056 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2910 raw1056; decide +kernel
    rw [heq]
    exact (canonical1056 hH).trans (sound2747 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2910 (1 : Fin 5)) =
      Sparse.eval value1561 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2910 (1 : Fin 5) = raw1485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2910 raw1485; decide +kernel
    rw [heq]
    exact (canonical1485 hH).trans (sound1561 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2910 (2 : Fin 5)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2910 (2 : Fin 5) = raw1542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2910 raw1542; decide +kernel
    rw [heq]
    exact (canonical1542 hH).trans (sound910 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2910 (3 : Fin 5)) =
      Sparse.eval value1559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2910 (3 : Fin 5) = raw1567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2910 raw1567; decide +kernel
    rw [heq]
    exact (canonical1567 hH).trans (sound1559 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2910 (4 : Fin 5)) =
      Sparse.eval value2401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2910 (4 : Fin 5) = raw1568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2910 raw1568; decide +kernel
    rw [heq]
    exact (canonical1568 hH).trans (sound2401 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2910 + (injectiveMoment H (mergeFirst pivotMatrix2910 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2910 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2910 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2910 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2910 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2910, value1559, value1561, value2401, value2747, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2911 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2911 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound2911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2911 = Sparse.eval value2911 (momentVector H) := by
  have heq : pivotMatrix2911 = (fun u v => node2911 (pivotPermutation2911 u) v) := by apply Matrix.ext; unfold pivotMatrix2911 node2911 pivotPermutation2911; decide +kernel
  have hmoment : injectiveMoment H node2911 = injectiveMoment H pivotMatrix2911 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2911 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2911 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2911 (0 : Fin 5)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2911 (0 : Fin 5) = raw1060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2911 raw1060; decide +kernel
    rw [heq]
    exact (canonical1060 hH).trans (sound2749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2911 (1 : Fin 5)) =
      Sparse.eval value1573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2911 (1 : Fin 5) = raw1487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2911 raw1487; decide +kernel
    rw [heq]
    exact (canonical1487 hH).trans (sound1573 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2911 (2 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2911 (2 : Fin 5) = raw1546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2911 raw1546; decide +kernel
    rw [heq]
    exact (canonical1546 hH).trans (sound2394 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2911 (3 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2911 (3 : Fin 5) = raw1569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2911 raw1569; decide +kernel
    rw [heq]
    exact (canonical1569 hH).trans (sound2394 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2911 (4 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2911 (4 : Fin 5) = raw1572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2911 raw1572; decide +kernel
    rw [heq]
    exact (canonical1572 hH).trans (sound2394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2911 + (injectiveMoment H (mergeFirst pivotMatrix2911 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2911 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2911 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2911 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2911 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2911, value1573, value2394, value2749, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2912 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2912 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem sound2912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2912 = Sparse.eval value2912 (momentVector H) := by
  have heq : pivotMatrix2912 = (fun u v => node2912 (pivotPermutation2912 u) v) := by apply Matrix.ext; unfold pivotMatrix2912 node2912 pivotPermutation2912; decide +kernel
  have hmoment : injectiveMoment H node2912 = injectiveMoment H pivotMatrix2912 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2912 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2912 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2912 (0 : Fin 5)) =
      Sparse.eval value1471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2912 (0 : Fin 5) = raw1061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2912 raw1061; decide +kernel
    rw [heq]
    exact (canonical1061 hH).trans (sound1471 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2912 (1 : Fin 5)) =
      Sparse.eval value1574 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2912 (1 : Fin 5) = raw1488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2912 raw1488; decide +kernel
    rw [heq]
    exact (canonical1488 hH).trans (sound1574 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2912 (2 : Fin 5)) =
      Sparse.eval value2393 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2912 (2 : Fin 5) = raw1547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2912 raw1547; decide +kernel
    rw [heq]
    exact (canonical1547 hH).trans (sound2393 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2912 (3 : Fin 5)) =
      Sparse.eval value2397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2912 (3 : Fin 5) = raw1570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2912 raw1570; decide +kernel
    rw [heq]
    exact (canonical1570 hH).trans (sound2397 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2912 (4 : Fin 5)) =
      Sparse.eval value1590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2912 (4 : Fin 5) = raw1573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2912 raw1573; decide +kernel
    rw [heq]
    exact (canonical1573 hH).trans (sound1590 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2912 + (injectiveMoment H (mergeFirst pivotMatrix2912 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2912 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2912 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2912 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2912 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2912, value1471, value1574, value1590, value2393, value2397, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2913 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2913 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound2913 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2913 = Sparse.eval value2913 (momentVector H) := by
  have heq : pivotMatrix2913 = (fun u v => node2913 (pivotPermutation2913 u) v) := by apply Matrix.ext; unfold pivotMatrix2913 node2913 pivotPermutation2913; decide +kernel
  have hmoment : injectiveMoment H node2913 = injectiveMoment H pivotMatrix2913 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2913 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2913 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2913 (0 : Fin 5)) =
      Sparse.eval value2747 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2913 (0 : Fin 5) = raw1062 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2913 raw1062; decide +kernel
    rw [heq]
    exact (canonical1062 hH).trans (sound2747 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2913 (1 : Fin 5)) =
      Sparse.eval value1575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2913 (1 : Fin 5) = raw1489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2913 raw1489; decide +kernel
    rw [heq]
    exact (canonical1489 hH).trans (sound1575 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2913 (2 : Fin 5)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2913 (2 : Fin 5) = raw1554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2913 raw1554; decide +kernel
    rw [heq]
    exact (canonical1554 hH).trans (sound2390 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2913 (3 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2913 (3 : Fin 5) = raw1575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2913 raw1575; decide +kernel
    rw [heq]
    exact (canonical1575 hH).trans (sound2400 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2913 (4 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2913 (4 : Fin 5) = raw1578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2913 raw1578; decide +kernel
    rw [heq]
    exact (canonical1578 hH).trans (sound2400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2913 + (injectiveMoment H (mergeFirst pivotMatrix2913 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2913 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2913 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2913 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2913 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2913, value1575, value2390, value2400, value2747, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2914 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2914 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound2914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2914 = Sparse.eval value2914 (momentVector H) := by
  have heq : pivotMatrix2914 = (fun u v => node2914 (pivotPermutation2914 u) v) := by apply Matrix.ext; unfold pivotMatrix2914 node2914 pivotPermutation2914; decide +kernel
  have hmoment : injectiveMoment H node2914 = injectiveMoment H pivotMatrix2914 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2914 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2914 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2914 (0 : Fin 5)) =
      Sparse.eval value2755 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2914 (0 : Fin 5) = raw1063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2914 raw1063; decide +kernel
    rw [heq]
    exact (canonical1063 hH).trans (sound2755 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2914 (1 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2914 (1 : Fin 5) = raw1490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2914 raw1490; decide +kernel
    rw [heq]
    exact (canonical1490 hH).trans (sound1576 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2914 (2 : Fin 5)) =
      Sparse.eval value2391 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2914 (2 : Fin 5) = raw1555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2914 raw1555; decide +kernel
    rw [heq]
    exact (canonical1555 hH).trans (sound2391 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2914 (3 : Fin 5)) =
      Sparse.eval value1592 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2914 (3 : Fin 5) = raw1576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2914 raw1576; decide +kernel
    rw [heq]
    exact (canonical1576 hH).trans (sound1592 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2914 (4 : Fin 5)) =
      Sparse.eval value2503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2914 (4 : Fin 5) = raw1579 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2914 raw1579; decide +kernel
    rw [heq]
    exact (canonical1579 hH).trans (sound2503 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2914 + (injectiveMoment H (mergeFirst pivotMatrix2914 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2914 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2914 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2914 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2914 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2914, value1576, value1592, value2391, value2503, value2755, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2915 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2915 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem sound2915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2915 = Sparse.eval value2915 (momentVector H) := by
  have heq : pivotMatrix2915 = (fun u v => node2915 (pivotPermutation2915 u) v) := by apply Matrix.ext; unfold pivotMatrix2915 node2915 pivotPermutation2915; decide +kernel
  have hmoment : injectiveMoment H node2915 = injectiveMoment H pivotMatrix2915 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2915 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2915 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2915 (0 : Fin 5)) =
      Sparse.eval value1472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2915 (0 : Fin 5) = raw1064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2915 raw1064; decide +kernel
    rw [heq]
    exact (canonical1064 hH).trans (sound1472 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2915 (1 : Fin 5)) =
      Sparse.eval value1577 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2915 (1 : Fin 5) = raw1491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2915 raw1491; decide +kernel
    rw [heq]
    exact (canonical1491 hH).trans (sound1577 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2915 (2 : Fin 5)) =
      Sparse.eval value2392 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2915 (2 : Fin 5) = raw1556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2915 raw1556; decide +kernel
    rw [heq]
    exact (canonical1556 hH).trans (sound2392 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2915 (3 : Fin 5)) =
      Sparse.eval value1593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2915 (3 : Fin 5) = raw1577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2915 raw1577; decide +kernel
    rw [heq]
    exact (canonical1577 hH).trans (sound1593 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2915 (4 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2915 (4 : Fin 5) = raw1580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2915 raw1580; decide +kernel
    rw [heq]
    exact (canonical1580 hH).trans (sound2400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2915 + (injectiveMoment H (mergeFirst pivotMatrix2915 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2915 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2915 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2915 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2915 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2915, value1472, value1577, value1593, value2392, value2400, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2916 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2916 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound2916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2916 = Sparse.eval value2916 (momentVector H) := by
  have heq : pivotMatrix2916 = (fun u v => node2916 (pivotPermutation2916 u) v) := by apply Matrix.ext; unfold pivotMatrix2916 node2916 pivotPermutation2916; decide +kernel
  have hmoment : injectiveMoment H node2916 = injectiveMoment H pivotMatrix2916 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2916 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2916 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2916 (0 : Fin 5)) =
      Sparse.eval value1471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2916 (0 : Fin 5) = raw1068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2916 raw1068; decide +kernel
    rw [heq]
    exact (canonical1068 hH).trans (sound1471 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2916 (1 : Fin 5)) =
      Sparse.eval value1578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2916 (1 : Fin 5) = raw1495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2916 raw1495; decide +kernel
    rw [heq]
    exact (canonical1495 hH).trans (sound1578 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2916 (2 : Fin 5)) =
      Sparse.eval value2401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2916 (2 : Fin 5) = raw1568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2916 raw1568; decide +kernel
    rw [heq]
    exact (canonical1568 hH).trans (sound2401 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2916 (3 : Fin 5)) =
      Sparse.eval value1599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2916 (3 : Fin 5) = raw1590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2916 raw1590; decide +kernel
    rw [heq]
    exact (canonical1590 hH).trans (sound1599 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2916 (4 : Fin 5)) =
      Sparse.eval value1600 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2916 (4 : Fin 5) = raw1592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2916 raw1592; decide +kernel
    rw [heq]
    exact (canonical1592 hH).trans (sound1600 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2916 + (injectiveMoment H (mergeFirst pivotMatrix2916 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2916 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2916 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2916 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2916 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2916, value1471, value1578, value1599, value1600, value2401, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2917 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2917 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound2917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2917 = Sparse.eval value2917 (momentVector H) := by
  have heq : pivotMatrix2917 = (fun u v => node2917 (pivotPermutation2917 u) v) := by apply Matrix.ext; unfold pivotMatrix2917 node2917 pivotPermutation2917; decide +kernel
  have hmoment : injectiveMoment H node2917 = injectiveMoment H pivotMatrix2917 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2917 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2917 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2917 (0 : Fin 5)) =
      Sparse.eval value1468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2917 (0 : Fin 5) = raw1070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2917 raw1070; decide +kernel
    rw [heq]
    exact (canonical1070 hH).trans (sound1468 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2917 (1 : Fin 5)) =
      Sparse.eval value1579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2917 (1 : Fin 5) = raw1497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2917 raw1497; decide +kernel
    rw [heq]
    exact (canonical1497 hH).trans (sound1579 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2917 (2 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2917 (2 : Fin 5) = raw1578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2917 raw1578; decide +kernel
    rw [heq]
    exact (canonical1578 hH).trans (sound2400 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2917 (3 : Fin 5)) =
      Sparse.eval value1575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2917 (3 : Fin 5) = raw1594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2917 raw1594; decide +kernel
    rw [heq]
    exact (canonical1594 hH).trans (sound1575 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2917 (4 : Fin 5)) =
      Sparse.eval value1601 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2917 (4 : Fin 5) = raw1597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2917 raw1597; decide +kernel
    rw [heq]
    exact (canonical1597 hH).trans (sound1601 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2917 + (injectiveMoment H (mergeFirst pivotMatrix2917 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2917 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2917 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2917 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2917 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2917, value1468, value1575, value1579, value1601, value2400, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2918 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2918 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2918 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2918 = Sparse.eval value2918 (momentVector H) := by
  have heq : pivotMatrix2918 = (fun u v => node2918 (pivotPermutation2918 u) v) := by apply Matrix.ext; unfold pivotMatrix2918 node2918 pivotPermutation2918; decide +kernel
  have hmoment : injectiveMoment H node2918 = injectiveMoment H pivotMatrix2918 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2918 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2918 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2918 (0 : Fin 5)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2918 (0 : Fin 5) = raw1071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2918 raw1071; decide +kernel
    rw [heq]
    exact (canonical1071 hH).trans (sound2749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2918 (1 : Fin 5)) =
      Sparse.eval value1580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2918 (1 : Fin 5) = raw1498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2918 raw1498; decide +kernel
    rw [heq]
    exact (canonical1498 hH).trans (sound1580 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2918 (2 : Fin 5)) =
      Sparse.eval value2503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2918 (2 : Fin 5) = raw1579 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2918 raw1579; decide +kernel
    rw [heq]
    exact (canonical1579 hH).trans (sound2503 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2918 (3 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2918 (3 : Fin 5) = raw1595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2918 raw1595; decide +kernel
    rw [heq]
    exact (canonical1595 hH).trans (sound1576 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2918 (4 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2918 (4 : Fin 5) = raw1598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2918 raw1598; decide +kernel
    rw [heq]
    exact (canonical1598 hH).trans (sound1576 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2918 + (injectiveMoment H (mergeFirst pivotMatrix2918 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2918 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2918 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2918 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2918 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2918, value1576, value1580, value2503, value2749, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2919 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2919 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2919 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2919 = Sparse.eval value2919 (momentVector H) := by
  have heq : pivotMatrix2919 = (fun u v => node2919 (pivotPermutation2919 u) v) := by apply Matrix.ext; unfold pivotMatrix2919 node2919 pivotPermutation2919; decide +kernel
  have hmoment : injectiveMoment H node2919 = injectiveMoment H pivotMatrix2919 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2919 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2919 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2919 (0 : Fin 5)) =
      Sparse.eval value2739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2919 (0 : Fin 5) = raw1073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2919 raw1073; decide +kernel
    rw [heq]
    exact (canonical1073 hH).trans (sound2739 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2919 (1 : Fin 5)) =
      Sparse.eval value1581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2919 (1 : Fin 5) = raw1500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2919 raw1500; decide +kernel
    rw [heq]
    exact (canonical1500 hH).trans (sound1581 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2919 (2 : Fin 5)) =
      Sparse.eval value2399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2919 (2 : Fin 5) = raw1586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2919 raw1586; decide +kernel
    rw [heq]
    exact (canonical1586 hH).trans (sound2399 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2919 (3 : Fin 5)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2919 (3 : Fin 5) = raw1601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2919 raw1601; decide +kernel
    rw [heq]
    exact (canonical1601 hH).trans (sound2402 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2919 (4 : Fin 5)) =
      Sparse.eval value1603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2919 (4 : Fin 5) = raw1603 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2919 raw1603; decide +kernel
    rw [heq]
    exact (canonical1603 hH).trans (sound1603 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2919 + (injectiveMoment H (mergeFirst pivotMatrix2919 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2919 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2919 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2919 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2919 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2919, value1581, value1603, value2399, value2402, value2739, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2920 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2920 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound2920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2920 = Sparse.eval value2920 (momentVector H) := by
  have heq : pivotMatrix2920 = (fun u v => node2920 (pivotPermutation2920 u) v) := by apply Matrix.ext; unfold pivotMatrix2920 node2920 pivotPermutation2920; decide +kernel
  have hmoment : injectiveMoment H node2920 = injectiveMoment H pivotMatrix2920 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2920 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2920 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2920 (0 : Fin 5)) =
      Sparse.eval value2596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2920 (0 : Fin 5) = raw1137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2920 raw1137; decide +kernel
    rw [heq]
    exact (canonical1137 hH).trans (sound2596 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2920 (1 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2920 (1 : Fin 5) = raw1578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2920 raw1578; decide +kernel
    rw [heq]
    exact (canonical1578 hH).trans (sound2400 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2920 (2 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2920 (2 : Fin 5) = raw1671 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2920 raw1671; decide +kernel
    rw [heq]
    exact (canonical1671 hH).trans (sound2400 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2920 (3 : Fin 5)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2920 (3 : Fin 5) = raw1677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2920 raw1677; decide +kernel
    rw [heq]
    exact (canonical1677 hH).trans (sound2390 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2920 (4 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2920 (4 : Fin 5) = raw1679 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2920 raw1679; decide +kernel
    rw [heq]
    exact (canonical1679 hH).trans (sound1585 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2920 + (injectiveMoment H (mergeFirst pivotMatrix2920 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2920 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2920 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2920 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2920 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2920, value1585, value2390, value2400, value2596, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2921 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2921 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2921 = Sparse.eval value2921 (momentVector H) := by
  have heq : pivotMatrix2921 = (fun u v => node2921 (pivotPermutation2921 u) v) := by apply Matrix.ext; unfold pivotMatrix2921 node2921 pivotPermutation2921; decide +kernel
  have hmoment : injectiveMoment H node2921 = injectiveMoment H pivotMatrix2921 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2921 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2921 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2921 (0 : Fin 5)) =
      Sparse.eval value2578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2921 (0 : Fin 5) = raw1138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2921 raw1138; decide +kernel
    rw [heq]
    exact (canonical1138 hH).trans (sound2578 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2921 (1 : Fin 5)) =
      Sparse.eval value2399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2921 (1 : Fin 5) = raw1586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2921 raw1586; decide +kernel
    rw [heq]
    exact (canonical1586 hH).trans (sound2399 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2921 (2 : Fin 5)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2921 (2 : Fin 5) = raw1672 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2921 raw1672; decide +kernel
    rw [heq]
    exact (canonical1672 hH).trans (sound2402 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2921 (3 : Fin 5)) =
      Sparse.eval value2399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2921 (3 : Fin 5) = raw1680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2921 raw1680; decide +kernel
    rw [heq]
    exact (canonical1680 hH).trans (sound2399 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2921 (4 : Fin 5)) =
      Sparse.eval value1595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2921 (4 : Fin 5) = raw1682 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2921 raw1682; decide +kernel
    rw [heq]
    exact (canonical1682 hH).trans (sound1595 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2921 + (injectiveMoment H (mergeFirst pivotMatrix2921 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2921 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2921 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2921 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2921 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2921, value1595, value2399, value2402, value2578, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2922 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2922 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2922 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2922 = Sparse.eval value2922 (momentVector H) := by
  have heq : pivotMatrix2922 = (fun u v => node2922 (pivotPermutation2922 u) v) := by apply Matrix.ext; unfold pivotMatrix2922 node2922 pivotPermutation2922; decide +kernel
  have hmoment : injectiveMoment H node2922 = injectiveMoment H pivotMatrix2922 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2922 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2922 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2922 (0 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2922 (0 : Fin 5) = raw3073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2922 raw3073; decide +kernel
    rw [heq]
    exact (canonical3073 hH).trans (sound2750 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2922 (1 : Fin 5)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2922 (1 : Fin 5) = raw1626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2922 raw1626; decide +kernel
    rw [heq]
    exact (canonical1626 hH).trans (sound2402 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2922 (2 : Fin 5)) =
      Sparse.eval value1581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2922 (2 : Fin 5) = raw1500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2922 raw1500; decide +kernel
    rw [heq]
    exact (canonical1500 hH).trans (sound1581 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2922 (3 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2922 (3 : Fin 5) = raw1492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2922 raw1492; decide +kernel
    rw [heq]
    exact (canonical1492 hH).trans (sound1576 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2922 (4 : Fin 5)) =
      Sparse.eval value1575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2922 (4 : Fin 5) = raw1489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2922 raw1489; decide +kernel
    rw [heq]
    exact (canonical1489 hH).trans (sound1575 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2922 + (injectiveMoment H (mergeFirst pivotMatrix2922 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2922 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2922 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2922 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2922 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2922, value1575, value1576, value1581, value2402, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2923 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2923 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem sound2923 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2923 = Sparse.eval value2923 (momentVector H) := by
  have heq : pivotMatrix2923 = (fun u v => node2923 (pivotPermutation2923 u) v) := by apply Matrix.ext; unfold pivotMatrix2923 node2923 pivotPermutation2923; decide +kernel
  have hmoment : injectiveMoment H node2923 = injectiveMoment H pivotMatrix2923 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2923 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2923 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2923 (0 : Fin 5)) =
      Sparse.eval value1672 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2923 (0 : Fin 5) = raw1882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2923 raw1882; decide +kernel
    rw [heq]
    exact (canonical1882 hH).trans (sound1672 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2923 (1 : Fin 5)) =
      Sparse.eval value1587 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2923 (1 : Fin 5) = raw1617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2923 raw1617; decide +kernel
    rw [heq]
    exact (canonical1617 hH).trans (sound1587 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2923 (2 : Fin 5)) =
      Sparse.eval value1587 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2923 (2 : Fin 5) = raw1559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2923 raw1559; decide +kernel
    rw [heq]
    exact (canonical1559 hH).trans (sound1587 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2923 (3 : Fin 5)) =
      Sparse.eval value1573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2923 (3 : Fin 5) = raw1549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2923 raw1549; decide +kernel
    rw [heq]
    exact (canonical1549 hH).trans (sound1573 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2923 (4 : Fin 5)) =
      Sparse.eval value1582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2923 (4 : Fin 5) = raw1548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2923 raw1548; decide +kernel
    rw [heq]
    exact (canonical1548 hH).trans (sound1582 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2923 + (injectiveMoment H (mergeFirst pivotMatrix2923 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2923 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2923 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2923 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2923 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2923, value1573, value1582, value1587, value1672, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2924 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2924 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem sound2924 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2924 = Sparse.eval value2924 (momentVector H) := by
  have heq : pivotMatrix2924 = (fun u v => node2924 (pivotPermutation2924 u) v) := by apply Matrix.ext; unfold pivotMatrix2924 node2924 pivotPermutation2924; decide +kernel
  have hmoment : injectiveMoment H node2924 = injectiveMoment H pivotMatrix2924 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2924 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2924 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2924 (0 : Fin 5)) =
      Sparse.eval value1674 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2924 (0 : Fin 5) = raw1884 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2924 raw1884; decide +kernel
    rw [heq]
    exact (canonical1884 hH).trans (sound1674 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2924 (1 : Fin 5)) =
      Sparse.eval value1588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2924 (1 : Fin 5) = raw1618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2924 raw1618; decide +kernel
    rw [heq]
    exact (canonical1618 hH).trans (sound1588 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2924 (2 : Fin 5)) =
      Sparse.eval value1588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2924 (2 : Fin 5) = raw1560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2924 raw1560; decide +kernel
    rw [heq]
    exact (canonical1560 hH).trans (sound1588 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2924 (3 : Fin 5)) =
      Sparse.eval value1586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2924 (3 : Fin 5) = raw1553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2924 raw1553; decide +kernel
    rw [heq]
    exact (canonical1553 hH).trans (sound1586 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2924 (4 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2924 (4 : Fin 5) = raw1552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2924 raw1552; decide +kernel
    rw [heq]
    exact (canonical1552 hH).trans (sound1585 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2924 + (injectiveMoment H (mergeFirst pivotMatrix2924 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2924 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2924 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2924 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2924 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2924, value1585, value1586, value1588, value1674, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2925 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2925 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem sound2925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2925 = Sparse.eval value2925 (momentVector H) := by
  have heq : pivotMatrix2925 = (fun u v => node2925 (pivotPermutation2925 u) v) := by apply Matrix.ext; unfold pivotMatrix2925 node2925 pivotPermutation2925; decide +kernel
  have hmoment : injectiveMoment H node2925 = injectiveMoment H pivotMatrix2925 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2925 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2925 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2925 (0 : Fin 5)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2925 (0 : Fin 5) = raw1895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2925 raw1895; decide +kernel
    rw [heq]
    exact (canonical1895 hH).trans (sound1680 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2925 (1 : Fin 5)) =
      Sparse.eval value1606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2925 (1 : Fin 5) = raw1619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2925 raw1619; decide +kernel
    rw [heq]
    exact (canonical1619 hH).trans (sound1606 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2925 (2 : Fin 5)) =
      Sparse.eval value1548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2925 (2 : Fin 5) = raw1571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2925 raw1571; decide +kernel
    rw [heq]
    exact (canonical1571 hH).trans (sound1548 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2925 (3 : Fin 5)) =
      Sparse.eval value1548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2925 (3 : Fin 5) = raw1564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2925 raw1564; decide +kernel
    rw [heq]
    exact (canonical1564 hH).trans (sound1548 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2925 (4 : Fin 5)) =
      Sparse.eval value1589 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2925 (4 : Fin 5) = raw1563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2925 raw1563; decide +kernel
    rw [heq]
    exact (canonical1563 hH).trans (sound1589 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2925 + (injectiveMoment H (mergeFirst pivotMatrix2925 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2925 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2925 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2925 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2925 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2925, value1548, value1589, value1606, value1680, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2926 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2926 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem sound2926 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2926 = Sparse.eval value2926 (momentVector H) := by
  have heq : pivotMatrix2926 = (fun u v => node2926 (pivotPermutation2926 u) v) := by apply Matrix.ext; unfold pivotMatrix2926 node2926 pivotPermutation2926; decide +kernel
  have hmoment : injectiveMoment H node2926 = injectiveMoment H pivotMatrix2926 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2926 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2926 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2926 (0 : Fin 5)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2926 (0 : Fin 5) = raw1905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2926 raw1905; decide +kernel
    rw [heq]
    exact (canonical1905 hH).trans (sound2676 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2926 (1 : Fin 5)) =
      Sparse.eval value1583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2926 (1 : Fin 5) = raw1622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2926 raw1622; decide +kernel
    rw [heq]
    exact (canonical1622 hH).trans (sound1583 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2926 (2 : Fin 5)) =
      Sparse.eval value1590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2926 (2 : Fin 5) = raw1582 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2926 raw1582; decide +kernel
    rw [heq]
    exact (canonical1582 hH).trans (sound1590 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2926 (3 : Fin 5)) =
      Sparse.eval value1590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2926 (3 : Fin 5) = raw1573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2926 raw1573; decide +kernel
    rw [heq]
    exact (canonical1573 hH).trans (sound1590 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2926 (4 : Fin 5)) =
      Sparse.eval value2394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2926 (4 : Fin 5) = raw1572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2926 raw1572; decide +kernel
    rw [heq]
    exact (canonical1572 hH).trans (sound2394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2926 + (injectiveMoment H (mergeFirst pivotMatrix2926 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2926 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2926 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2926 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2926 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2926, value1583, value1590, value2394, value2676, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2927 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2927 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound2927 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2927 = Sparse.eval value2927 (momentVector H) := by
  have heq : pivotMatrix2927 = (fun u v => node2927 (pivotPermutation2927 u) v) := by apply Matrix.ext; unfold pivotMatrix2927 node2927 pivotPermutation2927; decide +kernel
  have hmoment : injectiveMoment H node2927 = injectiveMoment H pivotMatrix2927 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2927 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2927 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2927 (0 : Fin 5)) =
      Sparse.eval value2620 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2927 (0 : Fin 5) = raw1907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2927 raw1907; decide +kernel
    rw [heq]
    exact (canonical1907 hH).trans (sound2620 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2927 (1 : Fin 5)) =
      Sparse.eval value1602 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2927 (1 : Fin 5) = raw1623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2927 raw1623; decide +kernel
    rw [heq]
    exact (canonical1623 hH).trans (sound1602 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2927 (2 : Fin 5)) =
      Sparse.eval value1594 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2927 (2 : Fin 5) = raw1583 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2927 raw1583; decide +kernel
    rw [heq]
    exact (canonical1583 hH).trans (sound1594 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2927 (3 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2927 (3 : Fin 5) = raw1575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2927 raw1575; decide +kernel
    rw [heq]
    exact (canonical1575 hH).trans (sound2400 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2927 (4 : Fin 5)) =
      Sparse.eval value1591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2927 (4 : Fin 5) = raw1574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2927 raw1574; decide +kernel
    rw [heq]
    exact (canonical1574 hH).trans (sound1591 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2927 + (injectiveMoment H (mergeFirst pivotMatrix2927 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2927 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2927 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2927 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2927 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2927, value1591, value1594, value1602, value2400, value2620, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2928 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2928 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2928 = Sparse.eval value2928 (momentVector H) := by
  have heq : pivotMatrix2928 = (fun u v => node2928 (pivotPermutation2928 u) v) := by apply Matrix.ext; unfold pivotMatrix2928 node2928 pivotPermutation2928; decide +kernel
  have hmoment : injectiveMoment H node2928 = injectiveMoment H pivotMatrix2928 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2928 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2928 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2928 (0 : Fin 5)) =
      Sparse.eval value2767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2928 (0 : Fin 5) = raw1908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2928 raw1908; decide +kernel
    rw [heq]
    exact (canonical1908 hH).trans (sound2767 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2928 (1 : Fin 5)) =
      Sparse.eval value1603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2928 (1 : Fin 5) = raw1624 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2928 raw1624; decide +kernel
    rw [heq]
    exact (canonical1624 hH).trans (sound1603 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2928 (2 : Fin 5)) =
      Sparse.eval value1595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2928 (2 : Fin 5) = raw1584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2928 raw1584; decide +kernel
    rw [heq]
    exact (canonical1584 hH).trans (sound1595 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2928 (3 : Fin 5)) =
      Sparse.eval value1592 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2928 (3 : Fin 5) = raw1576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2928 raw1576; decide +kernel
    rw [heq]
    exact (canonical1576 hH).trans (sound1592 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2928 (4 : Fin 5)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2928 (4 : Fin 5) = raw1575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2928 raw1575; decide +kernel
    rw [heq]
    exact (canonical1575 hH).trans (sound2400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2928 + (injectiveMoment H (mergeFirst pivotMatrix2928 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2928 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2928 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2928 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2928 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2928, value1592, value1595, value1603, value2400, value2767, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2929 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2929 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound2929 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2929 = Sparse.eval value2929 (momentVector H) := by
  have heq : pivotMatrix2929 = (fun u v => node2929 (pivotPermutation2929 u) v) := by apply Matrix.ext; unfold pivotMatrix2929 node2929 pivotPermutation2929; decide +kernel
  have hmoment : injectiveMoment H node2929 = injectiveMoment H pivotMatrix2929 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2929 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2929 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2929 (0 : Fin 5)) =
      Sparse.eval value1685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2929 (0 : Fin 5) = raw1909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2929 raw1909; decide +kernel
    rw [heq]
    exact (canonical1909 hH).trans (sound1685 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2929 (1 : Fin 5)) =
      Sparse.eval value1607 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2929 (1 : Fin 5) = raw1625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2929 raw1625; decide +kernel
    rw [heq]
    exact (canonical1625 hH).trans (sound1607 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2929 (2 : Fin 5)) =
      Sparse.eval value1596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2929 (2 : Fin 5) = raw1585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2929 raw1585; decide +kernel
    rw [heq]
    exact (canonical1585 hH).trans (sound1596 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2929 (3 : Fin 5)) =
      Sparse.eval value1593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2929 (3 : Fin 5) = raw1577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2929 raw1577; decide +kernel
    rw [heq]
    exact (canonical1577 hH).trans (sound1593 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2929 (4 : Fin 5)) =
      Sparse.eval value1592 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2929 (4 : Fin 5) = raw1576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2929 raw1576; decide +kernel
    rw [heq]
    exact (canonical1576 hH).trans (sound1592 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2929 + (injectiveMoment H (mergeFirst pivotMatrix2929 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2929 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2929 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2929 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2929 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2929, value1592, value1593, value1596, value1607, value1685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2930 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2930 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound2930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2930 = Sparse.eval value2930 (momentVector H) := by
  have heq : pivotMatrix2930 = (fun u v => node2930 (pivotPermutation2930 u) v) := by apply Matrix.ext; unfold pivotMatrix2930 node2930 pivotPermutation2930; decide +kernel
  have hmoment : injectiveMoment H node2930 = injectiveMoment H pivotMatrix2930 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2930 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2930 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2930 (0 : Fin 5)) =
      Sparse.eval value1686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2930 (0 : Fin 5) = raw1914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2930 raw1914; decide +kernel
    rw [heq]
    exact (canonical1914 hH).trans (sound1686 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2930 (1 : Fin 5)) =
      Sparse.eval value1608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2930 (1 : Fin 5) = raw1628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2930 raw1628; decide +kernel
    rw [heq]
    exact (canonical1628 hH).trans (sound1608 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2930 (2 : Fin 5)) =
      Sparse.eval value1597 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2930 (2 : Fin 5) = raw1588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2930 raw1588; decide +kernel
    rw [heq]
    exact (canonical1588 hH).trans (sound1597 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2930 (3 : Fin 5)) =
      Sparse.eval value1596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2930 (3 : Fin 5) = raw1585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2930 raw1585; decide +kernel
    rw [heq]
    exact (canonical1585 hH).trans (sound1596 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2930 (4 : Fin 5)) =
      Sparse.eval value1595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2930 (4 : Fin 5) = raw1584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2930 raw1584; decide +kernel
    rw [heq]
    exact (canonical1584 hH).trans (sound1595 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2930 + (injectiveMoment H (mergeFirst pivotMatrix2930 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2930 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2930 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2930 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2930 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2930, value1595, value1596, value1597, value1608, value1686, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2931 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2931 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound2931 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2931 = Sparse.eval value2931 (momentVector H) := by
  have heq : pivotMatrix2931 = (fun u v => node2931 (pivotPermutation2931 u) v) := by apply Matrix.ext; unfold pivotMatrix2931 node2931 pivotPermutation2931; decide +kernel
  have hmoment : injectiveMoment H node2931 = injectiveMoment H pivotMatrix2931 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2931 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2931 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2931 (0 : Fin 5)) =
      Sparse.eval value1687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2931 (0 : Fin 5) = raw1917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2931 raw1917; decide +kernel
    rw [heq]
    exact (canonical1917 hH).trans (sound1687 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2931 (1 : Fin 5)) =
      Sparse.eval value1609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2931 (1 : Fin 5) = raw1630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2931 raw1630; decide +kernel
    rw [heq]
    exact (canonical1630 hH).trans (sound1609 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2931 (2 : Fin 5)) =
      Sparse.eval value1575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2931 (2 : Fin 5) = raw1594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2931 raw1594; decide +kernel
    rw [heq]
    exact (canonical1594 hH).trans (sound1575 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2931 (3 : Fin 5)) =
      Sparse.eval value1599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2931 (3 : Fin 5) = raw1590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2931 raw1590; decide +kernel
    rw [heq]
    exact (canonical1590 hH).trans (sound1599 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2931 (4 : Fin 5)) =
      Sparse.eval value1598 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2931 (4 : Fin 5) = raw1589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2931 raw1589; decide +kernel
    rw [heq]
    exact (canonical1589 hH).trans (sound1598 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2931 + (injectiveMoment H (mergeFirst pivotMatrix2931 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2931 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2931 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2931 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2931 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2931, value1575, value1598, value1599, value1609, value1687, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2932 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2932 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound2932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2932 = Sparse.eval value2932 (momentVector H) := by
  have heq : pivotMatrix2932 = (fun u v => node2932 (pivotPermutation2932 u) v) := by apply Matrix.ext; unfold pivotMatrix2932 node2932 pivotPermutation2932; decide +kernel
  have hmoment : injectiveMoment H node2932 = injectiveMoment H pivotMatrix2932 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2932 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2932 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2932 (0 : Fin 5)) =
      Sparse.eval value1688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (0 : Fin 5) = raw1918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1918; decide +kernel
    rw [heq]
    exact (canonical1918 hH).trans (sound1688 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2932 (1 : Fin 5)) =
      Sparse.eval value1610 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (1 : Fin 5) = raw1631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1631; decide +kernel
    rw [heq]
    exact (canonical1631 hH).trans (sound1610 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2932 (2 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (2 : Fin 5) = raw1595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1595; decide +kernel
    rw [heq]
    exact (canonical1595 hH).trans (sound1576 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2932 (3 : Fin 5)) =
      Sparse.eval value1600 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (3 : Fin 5) = raw1591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1591; decide +kernel
    rw [heq]
    exact (canonical1591 hH).trans (sound1600 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2932 (4 : Fin 5)) =
      Sparse.eval value1599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2932 (4 : Fin 5) = raw1590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2932 raw1590; decide +kernel
    rw [heq]
    exact (canonical1590 hH).trans (sound1599 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2932 + (injectiveMoment H (mergeFirst pivotMatrix2932 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2932 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2932, value1576, value1599, value1600, value1610, value1688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2933 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2933 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound2933 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2933 = Sparse.eval value2933 (momentVector H) := by
  have heq : pivotMatrix2933 = (fun u v => node2933 (pivotPermutation2933 u) v) := by apply Matrix.ext; unfold pivotMatrix2933 node2933 pivotPermutation2933; decide +kernel
  have hmoment : injectiveMoment H node2933 = injectiveMoment H pivotMatrix2933 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2933 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2933 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2933 (0 : Fin 5)) =
      Sparse.eval value1690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2933 (0 : Fin 5) = raw1922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2933 raw1922; decide +kernel
    rw [heq]
    exact (canonical1922 hH).trans (sound1690 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2933 (1 : Fin 5)) =
      Sparse.eval value1611 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2933 (1 : Fin 5) = raw1633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2933 raw1633; decide +kernel
    rw [heq]
    exact (canonical1633 hH).trans (sound1611 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2933 (2 : Fin 5)) =
      Sparse.eval value1603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2933 (2 : Fin 5) = raw1602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2933 raw1602; decide +kernel
    rw [heq]
    exact (canonical1602 hH).trans (sound1603 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2933 (3 : Fin 5)) =
      Sparse.eval value1601 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2933 (3 : Fin 5) = raw1596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2933 raw1596; decide +kernel
    rw [heq]
    exact (canonical1596 hH).trans (sound1601 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2933 (4 : Fin 5)) =
      Sparse.eval value1576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2933 (4 : Fin 5) = raw1595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2933 raw1595; decide +kernel
    rw [heq]
    exact (canonical1595 hH).trans (sound1576 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2933 + (injectiveMoment H (mergeFirst pivotMatrix2933 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2933 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2933 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2933 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2933 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2933, value1576, value1601, value1603, value1611, value1690, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2934 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2934 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound2934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2934 = Sparse.eval value2934 (momentVector H) := by
  have heq : pivotMatrix2934 = (fun u v => node2934 (pivotPermutation2934 u) v) := by apply Matrix.ext; unfold pivotMatrix2934 node2934 pivotPermutation2934; decide +kernel
  have hmoment : injectiveMoment H node2934 = injectiveMoment H pivotMatrix2934 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2934 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2934 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2934 (0 : Fin 5)) =
      Sparse.eval value2619 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2934 (0 : Fin 5) = raw1925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2934 raw1925; decide +kernel
    rw [heq]
    exact (canonical1925 hH).trans (sound2619 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2934 (1 : Fin 5)) =
      Sparse.eval value1612 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2934 (1 : Fin 5) = raw1635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2934 raw1635; decide +kernel
    rw [heq]
    exact (canonical1635 hH).trans (sound1612 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2934 (2 : Fin 5)) =
      Sparse.eval value1604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2934 (2 : Fin 5) = raw1605 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2934 raw1605; decide +kernel
    rw [heq]
    exact (canonical1605 hH).trans (sound1604 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2934 (3 : Fin 5)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2934 (3 : Fin 5) = raw1601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2934 raw1601; decide +kernel
    rw [heq]
    exact (canonical1601 hH).trans (sound2402 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2934 (4 : Fin 5)) =
      Sparse.eval value1602 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2934 (4 : Fin 5) = raw1600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2934 raw1600; decide +kernel
    rw [heq]
    exact (canonical1600 hH).trans (sound1602 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2934 + (injectiveMoment H (mergeFirst pivotMatrix2934 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2934 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2934 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2934 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2934 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2934, value1602, value1604, value1612, value2402, value2619, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2935 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2935 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound2935 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2935 = Sparse.eval value2935 (momentVector H) := by
  have heq : pivotMatrix2935 = (fun u v => node2935 (pivotPermutation2935 u) v) := by apply Matrix.ext; unfold pivotMatrix2935 node2935 pivotPermutation2935; decide +kernel
  have hmoment : injectiveMoment H node2935 = injectiveMoment H pivotMatrix2935 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2935 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2935 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2935 (0 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2935 (0 : Fin 5) = raw1926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2935 raw1926; decide +kernel
    rw [heq]
    exact (canonical1926 hH).trans (sound2740 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2935 (1 : Fin 5)) =
      Sparse.eval value1613 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2935 (1 : Fin 5) = raw1636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2935 raw1636; decide +kernel
    rw [heq]
    exact (canonical1636 hH).trans (sound1613 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2935 (2 : Fin 5)) =
      Sparse.eval value1605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2935 (2 : Fin 5) = raw1606 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2935 raw1606; decide +kernel
    rw [heq]
    exact (canonical1606 hH).trans (sound1605 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2935 (3 : Fin 5)) =
      Sparse.eval value1603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2935 (3 : Fin 5) = raw1602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2935 raw1602; decide +kernel
    rw [heq]
    exact (canonical1602 hH).trans (sound1603 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2935 (4 : Fin 5)) =
      Sparse.eval value2402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2935 (4 : Fin 5) = raw1601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2935 raw1601; decide +kernel
    rw [heq]
    exact (canonical1601 hH).trans (sound2402 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2935 + (injectiveMoment H (mergeFirst pivotMatrix2935 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2935 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2935 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2935 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2935 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2935, value1603, value1605, value1613, value2402, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2936 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2936 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound2936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2936 = Sparse.eval value2936 (momentVector H) := by
  have heq : pivotMatrix2936 = (fun u v => node2936 (pivotPermutation2936 u) v) := by apply Matrix.ext; unfold pivotMatrix2936 node2936 pivotPermutation2936; decide +kernel
  have hmoment : injectiveMoment H node2936 = injectiveMoment H pivotMatrix2936 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2936 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2936 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2936 (0 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2936 (0 : Fin 5) = raw2017 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2936 raw2017; decide +kernel
    rw [heq]
    exact (canonical2017 hH).trans (sound1644 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2936 (1 : Fin 5)) =
      Sparse.eval value1551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2936 (1 : Fin 5) = raw1674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2936 raw1674; decide +kernel
    rw [heq]
    exact (canonical1674 hH).trans (sound1551 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2936 (2 : Fin 5)) =
      Sparse.eval value1551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2936 (2 : Fin 5) = raw1655 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2936 raw1655; decide +kernel
    rw [heq]
    exact (canonical1655 hH).trans (sound1551 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2936 (3 : Fin 5)) =
      Sparse.eval value1615 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2936 (3 : Fin 5) = raw1653 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2936 raw1653; decide +kernel
    rw [heq]
    exact (canonical1653 hH).trans (sound1615 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2936 (4 : Fin 5)) =
      Sparse.eval value1614 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2936 (4 : Fin 5) = raw1652 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2936 raw1652; decide +kernel
    rw [heq]
    exact (canonical1652 hH).trans (sound1614 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2936 + (injectiveMoment H (mergeFirst pivotMatrix2936 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2936 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2936 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2936 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2936 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2936, value1551, value1614, value1615, value1644, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2937 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2937 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound2937 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2937 = Sparse.eval value2937 (momentVector H) := by
  have heq : pivotMatrix2937 = (fun u v => node2937 (pivotPermutation2937 u) v) := by apply Matrix.ext; unfold pivotMatrix2937 node2937 pivotPermutation2937; decide +kernel
  have hmoment : injectiveMoment H node2937 = injectiveMoment H pivotMatrix2937 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2937 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2937 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2937 (0 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2937 (0 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2937 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2937 (1 : Fin 5)) =
      Sparse.eval value1605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2937 (1 : Fin 5) = raw1684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2937 raw1684; decide +kernel
    rw [heq]
    exact (canonical1684 hH).trans (sound1605 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2937 (2 : Fin 5)) =
      Sparse.eval value1617 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2937 (2 : Fin 5) = raw1663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2937 raw1663; decide +kernel
    rw [heq]
    exact (canonical1663 hH).trans (sound1617 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2937 (3 : Fin 5)) =
      Sparse.eval value1616 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2937 (3 : Fin 5) = raw1661 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2937 raw1661; decide +kernel
    rw [heq]
    exact (canonical1661 hH).trans (sound1616 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2937 (4 : Fin 5)) =
      Sparse.eval value1563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2937 (4 : Fin 5) = raw1660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2937 raw1660; decide +kernel
    rw [heq]
    exact (canonical1660 hH).trans (sound1563 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2937 + (injectiveMoment H (mergeFirst pivotMatrix2937 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2937 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2937 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2937 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2937 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2937, value1563, value1605, value1616, value1617, value1720, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2938 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2938 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound2938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2938 = Sparse.eval value2938 (momentVector H) := by
  have heq : pivotMatrix2938 = (fun u v => node2938 (pivotPermutation2938 u) v) := by apply Matrix.ext; unfold pivotMatrix2938 node2938 pivotPermutation2938; decide +kernel
  have hmoment : injectiveMoment H node2938 = injectiveMoment H pivotMatrix2938 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2938 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2938 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2938 (0 : Fin 5)) =
      Sparse.eval value2579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2938 (0 : Fin 5) = raw2061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2938 raw2061; decide +kernel
    rw [heq]
    exact (canonical2061 hH).trans (sound2579 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2938 (1 : Fin 5)) =
      Sparse.eval value1618 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2938 (1 : Fin 5) = raw1696 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2938 raw1696; decide +kernel
    rw [heq]
    exact (canonical1696 hH).trans (sound1618 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2938 (2 : Fin 5)) =
      Sparse.eval value1605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2938 (2 : Fin 5) = raw1684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2938 raw1684; decide +kernel
    rw [heq]
    exact (canonical1684 hH).trans (sound1605 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2938 (3 : Fin 5)) =
      Sparse.eval value1595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2938 (3 : Fin 5) = raw1681 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2938 raw1681; decide +kernel
    rw [heq]
    exact (canonical1681 hH).trans (sound1595 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2938 (4 : Fin 5)) =
      Sparse.eval value2399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2938 (4 : Fin 5) = raw1680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2938 raw1680; decide +kernel
    rw [heq]
    exact (canonical1680 hH).trans (sound2399 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2938 + (injectiveMoment H (mergeFirst pivotMatrix2938 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2938 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2938 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2938 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2938 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2938, value1595, value1605, value1618, value2399, value2579, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2939 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2939 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem sound2939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2939 = Sparse.eval value2939 (momentVector H) := by
  have heq : pivotMatrix2939 = (fun u v => node2939 (pivotPermutation2939 u) v) := by apply Matrix.ext; unfold pivotMatrix2939 node2939 pivotPermutation2939; decide +kernel
  have hmoment : injectiveMoment H node2939 = injectiveMoment H pivotMatrix2939 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2939 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2939 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2939 (0 : Fin 5)) =
      Sparse.eval value1627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2939 (0 : Fin 5) = raw2153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2939 raw2153; decide +kernel
    rw [heq]
    exact (canonical2153 hH).trans (sound1627 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2939 (1 : Fin 5)) =
      Sparse.eval value2737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2939 (1 : Fin 5) = raw1753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2939 raw1753; decide +kernel
    rw [heq]
    exact (canonical1753 hH).trans (sound2737 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2939 (2 : Fin 5)) =
      Sparse.eval value1620 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2939 (2 : Fin 5) = raw1744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2939 raw1744; decide +kernel
    rw [heq]
    exact (canonical1744 hH).trans (sound1620 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2939 (3 : Fin 5)) =
      Sparse.eval value2574 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2939 (3 : Fin 5) = raw1742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2939 raw1742; decide +kernel
    rw [heq]
    exact (canonical1742 hH).trans (sound2574 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2939 (4 : Fin 5)) =
      Sparse.eval value1544 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2939 (4 : Fin 5) = raw1741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2939 raw1741; decide +kernel
    rw [heq]
    exact (canonical1741 hH).trans (sound1544 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2939 + (injectiveMoment H (mergeFirst pivotMatrix2939 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2939 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2939 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2939 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2939 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2939, value1544, value1620, value1627, value2574, value2737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2940 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2940 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem sound2940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2940 = Sparse.eval value2940 (momentVector H) := by
  have heq : pivotMatrix2940 = (fun u v => node2940 (pivotPermutation2940 u) v) := by apply Matrix.ext; unfold pivotMatrix2940 node2940 pivotPermutation2940; decide +kernel
  have hmoment : injectiveMoment H node2940 = injectiveMoment H pivotMatrix2940 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2940 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2940 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2940 (0 : Fin 5)) =
      Sparse.eval value1454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2940 (0 : Fin 5) = raw1031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2940 raw1031; decide +kernel
    rw [heq]
    exact (canonical1031 hH).trans (sound1454 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2940 (1 : Fin 5)) =
      Sparse.eval value1619 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2940 (1 : Fin 5) = raw1743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2940 raw1743; decide +kernel
    rw [heq]
    exact (canonical1743 hH).trans (sound1619 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2940 (2 : Fin 5)) =
      Sparse.eval value1627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2940 (2 : Fin 5) = raw1822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2940 raw1822; decide +kernel
    rw [heq]
    exact (canonical1822 hH).trans (sound1627 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2940 (3 : Fin 5)) =
      Sparse.eval value2407 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2940 (3 : Fin 5) = raw1830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2940 raw1830; decide +kernel
    rw [heq]
    exact (canonical1830 hH).trans (sound2407 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2940 (4 : Fin 5)) =
      Sparse.eval value2408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2940 (4 : Fin 5) = raw1832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2940 raw1832; decide +kernel
    rw [heq]
    exact (canonical1832 hH).trans (sound2408 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2940 + (injectiveMoment H (mergeFirst pivotMatrix2940 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2940 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2940 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2940 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2940 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2940, value1454, value1619, value1627, value2407, value2408, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2941 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2941 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem sound2941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2941 = Sparse.eval value2941 (momentVector H) := by
  have heq : pivotMatrix2941 = (fun u v => node2941 (pivotPermutation2941 u) v) := by apply Matrix.ext; unfold pivotMatrix2941 node2941 pivotPermutation2941; decide +kernel
  have hmoment : injectiveMoment H node2941 = injectiveMoment H pivotMatrix2941 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2941 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2941 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2941 (0 : Fin 5)) =
      Sparse.eval value1455 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2941 (0 : Fin 5) = raw1032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2941 raw1032; decide +kernel
    rw [heq]
    exact (canonical1032 hH).trans (sound1455 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2941 (1 : Fin 5)) =
      Sparse.eval value1621 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2941 (1 : Fin 5) = raw1746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2941 raw1746; decide +kernel
    rw [heq]
    exact (canonical1746 hH).trans (sound1621 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2941 (2 : Fin 5)) =
      Sparse.eval value2405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2941 (2 : Fin 5) = raw1824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2941 raw1824; decide +kernel
    rw [heq]
    exact (canonical1824 hH).trans (sound2405 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2941 (3 : Fin 5)) =
      Sparse.eval value2413 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2941 (3 : Fin 5) = raw1838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2941 raw1838; decide +kernel
    rw [heq]
    exact (canonical1838 hH).trans (sound2413 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2941 (4 : Fin 5)) =
      Sparse.eval value1668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2941 (4 : Fin 5) = raw1840 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2941 raw1840; decide +kernel
    rw [heq]
    exact (canonical1840 hH).trans (sound1668 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2941 + (injectiveMoment H (mergeFirst pivotMatrix2941 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2941 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2941 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2941 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2941 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2941, value1455, value1621, value1668, value2405, value2413, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2942 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2942 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound2942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2942 = Sparse.eval value2942 (momentVector H) := by
  have heq : pivotMatrix2942 = (fun u v => node2942 (pivotPermutation2942 u) v) := by apply Matrix.ext; unfold pivotMatrix2942 node2942 pivotPermutation2942; decide +kernel
  have hmoment : injectiveMoment H node2942 = injectiveMoment H pivotMatrix2942 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2942 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2942 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2942 (0 : Fin 5)) =
      Sparse.eval value1456 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2942 (0 : Fin 5) = raw1033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2942 raw1033; decide +kernel
    rw [heq]
    exact (canonical1033 hH).trans (sound1456 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2942 (1 : Fin 5)) =
      Sparse.eval value1622 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2942 (1 : Fin 5) = raw1748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2942 raw1748; decide +kernel
    rw [heq]
    exact (canonical1748 hH).trans (sound1622 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2942 (2 : Fin 5)) =
      Sparse.eval value2411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2942 (2 : Fin 5) = raw1835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2942 raw1835; decide +kernel
    rw [heq]
    exact (canonical1835 hH).trans (sound2411 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2942 (3 : Fin 5)) =
      Sparse.eval value1669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2942 (3 : Fin 5) = raw1846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2942 raw1846; decide +kernel
    rw [heq]
    exact (canonical1846 hH).trans (sound1669 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2942 (4 : Fin 5)) =
      Sparse.eval value2415 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2942 (4 : Fin 5) = raw1848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2942 raw1848; decide +kernel
    rw [heq]
    exact (canonical1848 hH).trans (sound2415 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2942 + (injectiveMoment H (mergeFirst pivotMatrix2942 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2942 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2942 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2942 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2942 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2942, value1456, value1622, value1669, value2411, value2415, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2943 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2943 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem sound2943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2943 = Sparse.eval value2943 (momentVector H) := by
  have heq : pivotMatrix2943 = (fun u v => node2943 (pivotPermutation2943 u) v) := by apply Matrix.ext; unfold pivotMatrix2943 node2943 pivotPermutation2943; decide +kernel
  have hmoment : injectiveMoment H node2943 = injectiveMoment H pivotMatrix2943 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2943 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2943 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2943 (0 : Fin 5)) =
      Sparse.eval value1458 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2943 (0 : Fin 5) = raw1039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2943 raw1039; decide +kernel
    rw [heq]
    exact (canonical1039 hH).trans (sound1458 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2943 (1 : Fin 5)) =
      Sparse.eval value1630 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2943 (1 : Fin 5) = raw1760 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2943 raw1760; decide +kernel
    rw [heq]
    exact (canonical1760 hH).trans (sound1630 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2943 (2 : Fin 5)) =
      Sparse.eval value1630 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2943 (2 : Fin 5) = raw1870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2943 raw1870; decide +kernel
    rw [heq]
    exact (canonical1870 hH).trans (sound1630 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2943 (3 : Fin 5)) =
      Sparse.eval value2407 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2943 (3 : Fin 5) = raw1878 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2943 raw1878; decide +kernel
    rw [heq]
    exact (canonical1878 hH).trans (sound2407 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2943 (4 : Fin 5)) =
      Sparse.eval value2422 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2943 (4 : Fin 5) = raw1880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2943 raw1880; decide +kernel
    rw [heq]
    exact (canonical1880 hH).trans (sound2422 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2943 + (injectiveMoment H (mergeFirst pivotMatrix2943 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2943 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2943 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2943 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2943 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2943, value1458, value1630, value2407, value2422, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
