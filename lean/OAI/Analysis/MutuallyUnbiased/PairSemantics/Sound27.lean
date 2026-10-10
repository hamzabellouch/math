import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values27
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical71
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical207

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1728 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1728 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem sound1728 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1728 = Sparse.eval value1728 (momentVector H) := by
  have heq : pivotMatrix1728 = (fun u v => node1728 (pivotPermutation1728 u) v) := by apply Matrix.ext; unfold pivotMatrix1728 node1728 pivotPermutation1728; decide +kernel
  have hmoment : injectiveMoment H node1728 = injectiveMoment H pivotMatrix1728 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1728 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1728 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1728 (0 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1728 (0 : Fin 4) = raw3364 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1728 raw3364; decide +kernel
    rw [heq]
    exact (canonical3364 hH).trans (sound959 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1728 (1 : Fin 4)) =
      Sparse.eval value827 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1728 (1 : Fin 4) = raw2230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1728 raw2230; decide +kernel
    rw [heq]
    exact (canonical2230 hH).trans (sound827 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1728 (2 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1728 (2 : Fin 4) = raw2176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1728 raw2176; decide +kernel
    rw [heq]
    exact (canonical2176 hH).trans (sound502 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1728 (3 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1728 (3 : Fin 4) = raw2173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1728 raw2173; decide +kernel
    rw [heq]
    exact (canonical2173 hH).trans (sound1050 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1728 + (injectiveMoment H (mergeFirst pivotMatrix1728 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1728 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1728 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1728 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1728, value1050, value502, value827, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1729 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1729 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1729 = Sparse.eval value1729 (momentVector H) := by
  have heq : pivotMatrix1729 = (fun u v => node1729 (pivotPermutation1729 u) v) := by apply Matrix.ext; unfold pivotMatrix1729 node1729 pivotPermutation1729; decide +kernel
  have hmoment : injectiveMoment H node1729 = injectiveMoment H pivotMatrix1729 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1729 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1729 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1729 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1729 (0 : Fin 4) = raw3689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1729 raw3689; decide +kernel
    rw [heq]
    exact (canonical3689 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1729 (1 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1729 (1 : Fin 4) = raw2267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1729 raw2267; decide +kernel
    rw [heq]
    exact (canonical2267 hH).trans (sound837 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1729 (2 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1729 (2 : Fin 4) = raw2169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1729 raw2169; decide +kernel
    rw [heq]
    exact (canonical2169 hH).trans (sound488 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1729 (3 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1729 (3 : Fin 4) = raw2163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1729 raw2163; decide +kernel
    rw [heq]
    exact (canonical2163 hH).trans (sound497 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1729 + (injectiveMoment H (mergeFirst pivotMatrix1729 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1729 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1729 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1729 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1729, value1005, value488, value497, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1730 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1730 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound1730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1730 = Sparse.eval value1730 (momentVector H) := by
  have heq : pivotMatrix1730 = (fun u v => node1730 (pivotPermutation1730 u) v) := by apply Matrix.ext; unfold pivotMatrix1730 node1730 pivotPermutation1730; decide +kernel
  have hmoment : injectiveMoment H node1730 = injectiveMoment H pivotMatrix1730 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1730 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1730 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1730 (0 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1730 (0 : Fin 4) = raw3694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1730 raw3694; decide +kernel
    rw [heq]
    exact (canonical3694 hH).trans (sound939 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1730 (1 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1730 (1 : Fin 4) = raw2282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1730 raw2282; decide +kernel
    rw [heq]
    exact (canonical2282 hH).trans (sound1116 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1730 (2 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1730 (2 : Fin 4) = raw2176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1730 raw2176; decide +kernel
    rw [heq]
    exact (canonical2176 hH).trans (sound502 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1730 (3 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1730 (3 : Fin 4) = raw2172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1730 raw2172; decide +kernel
    rw [heq]
    exact (canonical2172 hH).trans (sound1100 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1730 + (injectiveMoment H (mergeFirst pivotMatrix1730 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1730 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1730 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1730 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1730, value1100, value1116, value502, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1731 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1731 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound1731 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1731 = Sparse.eval value1731 (momentVector H) := by
  have heq : pivotMatrix1731 = (fun u v => node1731 (pivotPermutation1731 u) v) := by apply Matrix.ext; unfold pivotMatrix1731 node1731 pivotPermutation1731; decide +kernel
  have hmoment : injectiveMoment H node1731 = injectiveMoment H pivotMatrix1731 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1731 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1731 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1731 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1731 (0 : Fin 4) = raw3696 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1731 raw3696; decide +kernel
    rw [heq]
    exact (canonical3696 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1731 (1 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1731 (1 : Fin 4) = raw2284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1731 raw2284; decide +kernel
    rw [heq]
    exact (canonical2284 hH).trans (sound835 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1731 (2 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1731 (2 : Fin 4) = raw2177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1731 raw2177; decide +kernel
    rw [heq]
    exact (canonical2177 hH).trans (sound502 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1731 (3 : Fin 4)) =
      Sparse.eval value500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1731 (3 : Fin 4) = raw2174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1731 raw2174; decide +kernel
    rw [heq]
    exact (canonical2174 hH).trans (sound500 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1731 + (injectiveMoment H (mergeFirst pivotMatrix1731 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1731 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1731 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1731 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1731, value1078, value500, value502, value835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1732 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1732 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem sound1732 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1732 = Sparse.eval value1732 (momentVector H) := by
  have heq : pivotMatrix1732 = (fun u v => node1732 (pivotPermutation1732 u) v) := by apply Matrix.ext; unfold pivotMatrix1732 node1732 pivotPermutation1732; decide +kernel
  have hmoment : injectiveMoment H node1732 = injectiveMoment H pivotMatrix1732 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1732 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1732 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1732 (0 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1732 (0 : Fin 4) = raw6609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1732 raw6609; decide +kernel
    rw [heq]
    exact (canonical6609 hH).trans (sound1096 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1732 (1 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1732 (1 : Fin 4) = raw2511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1732 raw2511; decide +kernel
    rw [heq]
    exact (canonical2511 hH).trans (sound514 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1732 (2 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1732 (2 : Fin 4) = raw2177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1732 raw2177; decide +kernel
    rw [heq]
    exact (canonical2177 hH).trans (sound502 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1732 (3 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1732 (3 : Fin 4) = raw2163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1732 raw2163; decide +kernel
    rw [heq]
    exact (canonical2163 hH).trans (sound497 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1732 + (injectiveMoment H (mergeFirst pivotMatrix1732 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1732 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1732 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1732 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1732, value1096, value497, value502, value514, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1733 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1733 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound1733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1733 = Sparse.eval value1733 (momentVector H) := by
  have heq : pivotMatrix1733 = (fun u v => node1733 (pivotPermutation1733 u) v) := by apply Matrix.ext; unfold pivotMatrix1733 node1733 pivotPermutation1733; decide +kernel
  have hmoment : injectiveMoment H node1733 = injectiveMoment H pivotMatrix1733 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1733 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1733 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1733 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1733 (0 : Fin 4) = raw6611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1733 raw6611; decide +kernel
    rw [heq]
    exact (canonical6611 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1733 (1 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1733 (1 : Fin 4) = raw2512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1733 raw2512; decide +kernel
    rw [heq]
    exact (canonical2512 hH).trans (sound517 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1733 (2 : Fin 4)) =
      Sparse.eval value500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1733 (2 : Fin 4) = raw2178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1733 raw2178; decide +kernel
    rw [heq]
    exact (canonical2178 hH).trans (sound500 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1733 (3 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1733 (3 : Fin 4) = raw2166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1733 raw2166; decide +kernel
    rw [heq]
    exact (canonical2166 hH).trans (sound484 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1733 + (injectiveMoment H (mergeFirst pivotMatrix1733 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1733 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1733 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1733 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1733, value1078, value484, value500, value517, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1734 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1734 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem sound1734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1734 = Sparse.eval value1734 (momentVector H) := by
  have heq : pivotMatrix1734 = (fun u v => node1734 (pivotPermutation1734 u) v) := by apply Matrix.ext; unfold pivotMatrix1734 node1734 pivotPermutation1734; decide +kernel
  have hmoment : injectiveMoment H node1734 = injectiveMoment H pivotMatrix1734 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1734 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1734 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1734 (0 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1734 (0 : Fin 4) = raw6394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1734 raw6394; decide +kernel
    rw [heq]
    exact (canonical6394 hH).trans (sound1033 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1734 (1 : Fin 4)) =
      Sparse.eval value518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1734 (1 : Fin 4) = raw2509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1734 raw2509; decide +kernel
    rw [heq]
    exact (canonical2509 hH).trans (sound518 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1734 (2 : Fin 4)) =
      Sparse.eval value500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1734 (2 : Fin 4) = raw2178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1734 raw2178; decide +kernel
    rw [heq]
    exact (canonical2178 hH).trans (sound500 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1734 (3 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1734 (3 : Fin 4) = raw2168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1734 raw2168; decide +kernel
    rw [heq]
    exact (canonical2168 hH).trans (sound1059 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1734 + (injectiveMoment H (mergeFirst pivotMatrix1734 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1734 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1734 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1734 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1734, value1033, value1059, value500, value518, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1735 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1735 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound1735 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1735 = Sparse.eval value1735 (momentVector H) := by
  have heq : pivotMatrix1735 = (fun u v => node1735 (pivotPermutation1735 u) v) := by apply Matrix.ext; unfold pivotMatrix1735 node1735 pivotPermutation1735; decide +kernel
  have hmoment : injectiveMoment H node1735 = injectiveMoment H pivotMatrix1735 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1735 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1735 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1735 (0 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1735 (0 : Fin 4) = raw6396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1735 raw6396; decide +kernel
    rw [heq]
    exact (canonical6396 hH).trans (sound998 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1735 (1 : Fin 4)) =
      Sparse.eval value821 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1735 (1 : Fin 4) = raw2510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1735 raw2510; decide +kernel
    rw [heq]
    exact (canonical2510 hH).trans (sound821 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1735 (2 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1735 (2 : Fin 4) = raw2179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1735 raw2179; decide +kernel
    rw [heq]
    exact (canonical2179 hH).trans (sound1100 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1735 (3 : Fin 4)) =
      Sparse.eval value499 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1735 (3 : Fin 4) = raw2171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1735 raw2171; decide +kernel
    rw [heq]
    exact (canonical2171 hH).trans (sound499 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1735 + (injectiveMoment H (mergeFirst pivotMatrix1735 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1735 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1735 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1735 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1735, value1100, value499, value821, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1736 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1736 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem sound1736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1736 = Sparse.eval value1736 (momentVector H) := by
  have heq : pivotMatrix1736 = (fun u v => node1736 (pivotPermutation1736 u) v) := by apply Matrix.ext; unfold pivotMatrix1736 node1736 pivotPermutation1736; decide +kernel
  have hmoment : injectiveMoment H node1736 = injectiveMoment H pivotMatrix1736 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1736 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1736 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1736 (0 : Fin 4)) =
      Sparse.eval value1129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1736 (0 : Fin 4) = raw1199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1736 raw1199; decide +kernel
    rw [heq]
    exact (canonical1199 hH).trans (sound1129 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1736 (1 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1736 (1 : Fin 4) = raw2176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1736 raw2176; decide +kernel
    rw [heq]
    exact (canonical2176 hH).trans (sound502 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1736 (2 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1736 (2 : Fin 4) = raw2282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1736 raw2282; decide +kernel
    rw [heq]
    exact (canonical2282 hH).trans (sound1116 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1736 (3 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1736 (3 : Fin 4) = raw2285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1736 raw2285; decide +kernel
    rw [heq]
    exact (canonical2285 hH).trans (sound835 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1736 + (injectiveMoment H (mergeFirst pivotMatrix1736 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1736 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1736 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1736 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1736, value1116, value1129, value502, value835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1737 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1737 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem sound1737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1737 = Sparse.eval value1737 (momentVector H) := by
  have heq : pivotMatrix1737 = (fun u v => node1737 (pivotPermutation1737 u) v) := by apply Matrix.ext; unfold pivotMatrix1737 node1737 pivotPermutation1737; decide +kernel
  have hmoment : injectiveMoment H node1737 = injectiveMoment H pivotMatrix1737 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1737 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1737 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1737 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1737 (0 : Fin 4) = raw1216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1737 raw1216; decide +kernel
    rw [heq]
    exact (canonical1216 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1737 (1 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1737 (1 : Fin 4) = raw2198 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1737 raw2198; decide +kernel
    rw [heq]
    exact (canonical2198 hH).trans (sound1263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1737 (2 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1737 (2 : Fin 4) = raw2312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1737 raw2312; decide +kernel
    rw [heq]
    exact (canonical2312 hH).trans (sound288 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1737 (3 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1737 (3 : Fin 4) = raw2337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1737 raw2337; decide +kernel
    rw [heq]
    exact (canonical2337 hH).trans (sound1053 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1737 + (injectiveMoment H (mergeFirst pivotMatrix1737 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1737 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1737 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1737 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1737, value1053, value1263, value288, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1738 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1738 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem sound1738 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1738 = Sparse.eval value1738 (momentVector H) := by
  have heq : pivotMatrix1738 = (fun u v => node1738 (pivotPermutation1738 u) v) := by apply Matrix.ext; unfold pivotMatrix1738 node1738 pivotPermutation1738; decide +kernel
  have hmoment : injectiveMoment H node1738 = injectiveMoment H pivotMatrix1738 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1738 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1738 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1738 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1738 (0 : Fin 4) = raw1224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1738 raw1224; decide +kernel
    rw [heq]
    exact (canonical1224 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1738 (1 : Fin 4)) =
      Sparse.eval value1244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1738 (1 : Fin 4) = raw2203 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1738 raw2203; decide +kernel
    rw [heq]
    exact (canonical2203 hH).trans (sound1244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1738 (2 : Fin 4)) =
      Sparse.eval value1247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1738 (2 : Fin 4) = raw2358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1738 raw2358; decide +kernel
    rw [heq]
    exact (canonical2358 hH).trans (sound1247 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1738 (3 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1738 (3 : Fin 4) = raw2360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1738 raw2360; decide +kernel
    rw [heq]
    exact (canonical2360 hH).trans (sound1047 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1738 + (injectiveMoment H (mergeFirst pivotMatrix1738 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1738 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1738 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1738 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1738, value1047, value1244, value1247, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1739 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1739 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound1739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1739 = Sparse.eval value1739 (momentVector H) := by
  have heq : pivotMatrix1739 = (fun u v => node1739 (pivotPermutation1739 u) v) := by apply Matrix.ext; unfold pivotMatrix1739 node1739 pivotPermutation1739; decide +kernel
  have hmoment : injectiveMoment H node1739 = injectiveMoment H pivotMatrix1739 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1739 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1739 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1739 (0 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1739 (0 : Fin 4) = raw1250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1739 raw1250; decide +kernel
    rw [heq]
    exact (canonical1250 hH).trans (sound1104 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1739 (1 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1739 (1 : Fin 4) = raw2282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1739 raw2282; decide +kernel
    rw [heq]
    exact (canonical2282 hH).trans (sound1116 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1739 (2 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1739 (2 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1739 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1739 (3 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1739 (3 : Fin 4) = raw2437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1739 raw2437; decide +kernel
    rw [heq]
    exact (canonical2437 hH).trans (sound1110 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1739 + (injectiveMoment H (mergeFirst pivotMatrix1739 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1739 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1739 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1739 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1739, value1104, value1110, value1116, value1123, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1740 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1740 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound1740 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1740 = Sparse.eval value1740 (momentVector H) := by
  have heq : pivotMatrix1740 = (fun u v => node1740 (pivotPermutation1740 u) v) := by apply Matrix.ext; unfold pivotMatrix1740 node1740 pivotPermutation1740; decide +kernel
  have hmoment : injectiveMoment H node1740 = injectiveMoment H pivotMatrix1740 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1740 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1740 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1740 (0 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1740 (0 : Fin 4) = raw1266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1740 raw1266; decide +kernel
    rw [heq]
    exact (canonical1266 hH).trans (sound995 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1740 (1 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1740 (1 : Fin 4) = raw2359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1740 raw2359; decide +kernel
    rw [heq]
    exact (canonical2359 hH).trans (sound1260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1740 (2 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1740 (2 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1740 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1740 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1740 (3 : Fin 4) = raw2474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1740 raw2474; decide +kernel
    rw [heq]
    exact (canonical2474 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1740 + (injectiveMoment H (mergeFirst pivotMatrix1740 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1740 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1740 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1740 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1740, value1040, value1260, value514, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1741 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1741 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound1741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1741 = Sparse.eval value1741 (momentVector H) := by
  have heq : pivotMatrix1741 = (fun u v => node1741 (pivotPermutation1741 u) v) := by apply Matrix.ext; unfold pivotMatrix1741 node1741 pivotPermutation1741; decide +kernel
  have hmoment : injectiveMoment H node1741 = injectiveMoment H pivotMatrix1741 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1741 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1741 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1741 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1741 (0 : Fin 4) = raw1269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1741 raw1269; decide +kernel
    rw [heq]
    exact (canonical1269 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1741 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1741 (1 : Fin 4) = raw2437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1741 raw2437; decide +kernel
    rw [heq]
    exact (canonical2437 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1741 (2 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1741 (2 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1741 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1741 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1741 (3 : Fin 4) = raw2492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1741 raw2492; decide +kernel
    rw [heq]
    exact (canonical2492 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1741 + (injectiveMoment H (mergeFirst pivotMatrix1741 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1741 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1741 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1741 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1741, value1036, value1078, value1110, value517, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1742 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1742 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem sound1742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1742 = Sparse.eval value1742 (momentVector H) := by
  have heq : pivotMatrix1742 = (fun u v => node1742 (pivotPermutation1742 u) v) := by apply Matrix.ext; unfold pivotMatrix1742 node1742 pivotPermutation1742; decide +kernel
  have hmoment : injectiveMoment H node1742 = injectiveMoment H pivotMatrix1742 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1742 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1742 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1742 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1742 (0 : Fin 4) = raw1292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1742 raw1292; decide +kernel
    rw [heq]
    exact (canonical1292 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1742 (1 : Fin 4)) =
      Sparse.eval value1316 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1742 (1 : Fin 4) = raw2185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1742 raw2185; decide +kernel
    rw [heq]
    exact (canonical2185 hH).trans (sound1316 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1742 (2 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1742 (2 : Fin 4) = raw2263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1742 raw2263; decide +kernel
    rw [heq]
    exact (canonical2263 hH).trans (sound1284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1742 (3 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1742 (3 : Fin 4) = raw2272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1742 raw2272; decide +kernel
    rw [heq]
    exact (canonical2272 hH).trans (sound1111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1742 + (injectiveMoment H (mergeFirst pivotMatrix1742 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1742 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1742 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1742 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1742, value1059, value1111, value1284, value1316, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1743 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1743 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem sound1743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1743 = Sparse.eval value1743 (momentVector H) := by
  have heq : pivotMatrix1743 = (fun u v => node1743 (pivotPermutation1743 u) v) := by apply Matrix.ext; unfold pivotMatrix1743 node1743 pivotPermutation1743; decide +kernel
  have hmoment : injectiveMoment H node1743 = injectiveMoment H pivotMatrix1743 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1743 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1743 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1743 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1743 (0 : Fin 4) = raw1294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1743 raw1294; decide +kernel
    rw [heq]
    exact (canonical1294 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1743 (1 : Fin 4)) =
      Sparse.eval value1311 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1743 (1 : Fin 4) = raw2187 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1743 raw2187; decide +kernel
    rw [heq]
    exact (canonical2187 hH).trans (sound1311 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1743 (2 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1743 (2 : Fin 4) = raw2267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1743 raw2267; decide +kernel
    rw [heq]
    exact (canonical2267 hH).trans (sound837 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1743 (3 : Fin 4)) =
      Sparse.eval value1281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1743 (3 : Fin 4) = raw2277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1743 raw2277; decide +kernel
    rw [heq]
    exact (canonical2277 hH).trans (sound1281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1743 + (injectiveMoment H (mergeFirst pivotMatrix1743 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1743 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1743 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1743 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1743, value1059, value1281, value1311, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1744 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1744 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound1744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1744 = Sparse.eval value1744 (momentVector H) := by
  have heq : pivotMatrix1744 = (fun u v => node1744 (pivotPermutation1744 u) v) := by apply Matrix.ext; unfold pivotMatrix1744 node1744 pivotPermutation1744; decide +kernel
  have hmoment : injectiveMoment H node1744 = injectiveMoment H pivotMatrix1744 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1744 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1744 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1744 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1744 (0 : Fin 4) = raw1304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1744 raw1304; decide +kernel
    rw [heq]
    exact (canonical1304 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1744 (1 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1744 (1 : Fin 4) = raw2263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1744 raw2263; decide +kernel
    rw [heq]
    exact (canonical2263 hH).trans (sound1284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1744 (2 : Fin 4)) =
      Sparse.eval value840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1744 (2 : Fin 4) = raw2391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1744 raw2391; decide +kernel
    rw [heq]
    exact (canonical2391 hH).trans (sound840 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1744 (3 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1744 (3 : Fin 4) = raw2397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1744 raw2397; decide +kernel
    rw [heq]
    exact (canonical2397 hH).trans (sound1111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1744 + (injectiveMoment H (mergeFirst pivotMatrix1744 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1744 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1744 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1744 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1744, value1111, value1284, value831, value840, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1745 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1745 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1745 = Sparse.eval value1745 (momentVector H) := by
  have heq : pivotMatrix1745 = (fun u v => node1745 (pivotPermutation1745 u) v) := by apply Matrix.ext; unfold pivotMatrix1745 node1745 pivotPermutation1745; decide +kernel
  have hmoment : injectiveMoment H node1745 = injectiveMoment H pivotMatrix1745 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1745 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1745 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1745 (0 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (0 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1745 (1 : Fin 4)) =
      Sparse.eval value1259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (1 : Fin 4) = raw2283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw2283; decide +kernel
    rw [heq]
    exact (canonical2283 hH).trans (sound1259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1745 (2 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (2 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1745 (3 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1745 (3 : Fin 4) = raw2406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1745 raw2406; decide +kernel
    rw [heq]
    exact (canonical2406 hH).trans (sound838 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1745 + (injectiveMoment H (mergeFirst pivotMatrix1745 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1745 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1745 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1745 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1745, value1259, value513, value828, value838, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1746 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1746 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound1746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1746 = Sparse.eval value1746 (momentVector H) := by
  have heq : pivotMatrix1746 = (fun u v => node1746 (pivotPermutation1746 u) v) := by apply Matrix.ext; unfold pivotMatrix1746 node1746 pivotPermutation1746; decide +kernel
  have hmoment : injectiveMoment H node1746 = injectiveMoment H pivotMatrix1746 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1746 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1746 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1746 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (0 : Fin 4) = raw1309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw1309; decide +kernel
    rw [heq]
    exact (canonical1309 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1746 (1 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (1 : Fin 4) = raw2293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw2293; decide +kernel
    rw [heq]
    exact (canonical2293 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1746 (2 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (2 : Fin 4) = raw2411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw2411; decide +kernel
    rw [heq]
    exact (canonical2411 hH).trans (sound291 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1746 (3 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (3 : Fin 4) = raw2419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw2419; decide +kernel
    rw [heq]
    exact (canonical2419 hH).trans (sound1107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1746 + (injectiveMoment H (mergeFirst pivotMatrix1746 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1746 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1746 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1746 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1746, value1027, value1107, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1747 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1747 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1747 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1747 = Sparse.eval value1747 (momentVector H) := by
  have heq : pivotMatrix1747 = (fun u v => node1747 (pivotPermutation1747 u) v) := by apply Matrix.ext; unfold pivotMatrix1747 node1747 pivotPermutation1747; decide +kernel
  have hmoment : injectiveMoment H node1747 = injectiveMoment H pivotMatrix1747 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1747 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1747 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1747 (0 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1747 (0 : Fin 4) = raw1312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1747 raw1312; decide +kernel
    rw [heq]
    exact (canonical1312 hH).trans (sound1033 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1747 (1 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1747 (1 : Fin 4) = raw2298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1747 raw2298; decide +kernel
    rw [heq]
    exact (canonical2298 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1747 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1747 (2 : Fin 4) = raw2413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1747 raw2413; decide +kernel
    rw [heq]
    exact (canonical2413 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1747 (3 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1747 (3 : Fin 4) = raw2424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1747 raw2424; decide +kernel
    rw [heq]
    exact (canonical2424 hH).trans (sound1110 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1747 + (injectiveMoment H (mergeFirst pivotMatrix1747 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1747 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1747 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1747 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1747, value1033, value1110, value1265, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1748 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1748 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1748 = Sparse.eval value1748 (momentVector H) := by
  have heq : pivotMatrix1748 = (fun u v => node1748 (pivotPermutation1748 u) v) := by apply Matrix.ext; unfold pivotMatrix1748 node1748 pivotPermutation1748; decide +kernel
  have hmoment : injectiveMoment H node1748 = injectiveMoment H pivotMatrix1748 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1748 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1748 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1748 (0 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1748 (0 : Fin 4) = raw1315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1748 raw1315; decide +kernel
    rw [heq]
    exact (canonical1315 hH).trans (sound1237 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1748 (1 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1748 (1 : Fin 4) = raw2308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1748 raw2308; decide +kernel
    rw [heq]
    exact (canonical2308 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1748 (2 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1748 (2 : Fin 4) = raw2435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1748 raw2435; decide +kernel
    rw [heq]
    exact (canonical2435 hH).trans (sound1096 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1748 (3 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1748 (3 : Fin 4) = raw2438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1748 raw2438; decide +kernel
    rw [heq]
    exact (canonical2438 hH).trans (sound1039 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1748 + (injectiveMoment H (mergeFirst pivotMatrix1748 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1748 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1748 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1748 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1748, value1039, value1096, value1237, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1749 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1749 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound1749 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1749 = Sparse.eval value1749 (momentVector H) := by
  have heq : pivotMatrix1749 = (fun u v => node1749 (pivotPermutation1749 u) v) := by apply Matrix.ext; unfold pivotMatrix1749 node1749 pivotPermutation1749; decide +kernel
  have hmoment : injectiveMoment H node1749 = injectiveMoment H pivotMatrix1749 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1749 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1749 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1749 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (0 : Fin 4) = raw1320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw1320; decide +kernel
    rw [heq]
    exact (canonical1320 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1749 (1 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (1 : Fin 4) = raw2337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw2337; decide +kernel
    rw [heq]
    exact (canonical2337 hH).trans (sound1053 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1749 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (2 : Fin 4) = raw2441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw2441; decide +kernel
    rw [heq]
    exact (canonical2441 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1749 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1749 (3 : Fin 4) = raw2451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1749 raw2451; decide +kernel
    rw [heq]
    exact (canonical2451 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1749 + (injectiveMoment H (mergeFirst pivotMatrix1749 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1749 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1749 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1749 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1749, value1027, value1040, value1053, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1750 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1750 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound1750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1750 = Sparse.eval value1750 (momentVector H) := by
  have heq : pivotMatrix1750 = (fun u v => node1750 (pivotPermutation1750 u) v) := by apply Matrix.ext; unfold pivotMatrix1750 node1750 pivotPermutation1750; decide +kernel
  have hmoment : injectiveMoment H node1750 = injectiveMoment H pivotMatrix1750 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1750 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1750 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1750 (0 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1750 (0 : Fin 4) = raw1322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1750 raw1322; decide +kernel
    rw [heq]
    exact (canonical1322 hH).trans (sound1237 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1750 (1 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1750 (1 : Fin 4) = raw2359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1750 raw2359; decide +kernel
    rw [heq]
    exact (canonical2359 hH).trans (sound1260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1750 (2 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1750 (2 : Fin 4) = raw2458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1750 raw2458; decide +kernel
    rw [heq]
    exact (canonical2458 hH).trans (sound1260 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1750 (3 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1750 (3 : Fin 4) = raw2462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1750 raw2462; decide +kernel
    rw [heq]
    exact (canonical2462 hH).trans (sound1044 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1750 + (injectiveMoment H (mergeFirst pivotMatrix1750 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1750 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1750 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1750 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1750, value1044, value1237, value1260, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1751 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1751 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound1751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1751 = Sparse.eval value1751 (momentVector H) := by
  have heq : pivotMatrix1751 = (fun u v => node1751 (pivotPermutation1751 u) v) := by apply Matrix.ext; unfold pivotMatrix1751 node1751 pivotPermutation1751; decide +kernel
  have hmoment : injectiveMoment H node1751 = injectiveMoment H pivotMatrix1751 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1751 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1751 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1751 (0 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1751 (0 : Fin 4) = raw1323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1751 raw1323; decide +kernel
    rw [heq]
    exact (canonical1323 hH).trans (sound1033 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1751 (1 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1751 (1 : Fin 4) = raw2360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1751 raw2360; decide +kernel
    rw [heq]
    exact (canonical2360 hH).trans (sound1047 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1751 (2 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1751 (2 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1751 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1751 (3 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1751 (3 : Fin 4) = raw2463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1751 raw2463; decide +kernel
    rw [heq]
    exact (canonical2463 hH).trans (sound1044 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1751 + (injectiveMoment H (mergeFirst pivotMatrix1751 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1751 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1751 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1751 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1751, value1033, value1044, value1047, value1078, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1752 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1752 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound1752 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1752 = Sparse.eval value1752 (momentVector H) := by
  have heq : pivotMatrix1752 = (fun u v => node1752 (pivotPermutation1752 u) v) := by apply Matrix.ext; unfold pivotMatrix1752 node1752 pivotPermutation1752; decide +kernel
  have hmoment : injectiveMoment H node1752 = injectiveMoment H pivotMatrix1752 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1752 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1752 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1752 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1752 (0 : Fin 4) = raw1326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1752 raw1326; decide +kernel
    rw [heq]
    exact (canonical1326 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1752 (1 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1752 (1 : Fin 4) = raw2438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1752 raw2438; decide +kernel
    rw [heq]
    exact (canonical2438 hH).trans (sound1039 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1752 (2 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1752 (2 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1752 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1752 (3 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1752 (3 : Fin 4) = raw2487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1752 raw2487; decide +kernel
    rw [heq]
    exact (canonical2487 hH).trans (sound1005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1752 + (injectiveMoment H (mergeFirst pivotMatrix1752 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1752 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1752 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1752 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1752, value1005, value1027, value1039, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1753 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1753 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem sound1753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1753 = Sparse.eval value1753 (momentVector H) := by
  have heq : pivotMatrix1753 = (fun u v => node1753 (pivotPermutation1753 u) v) := by apply Matrix.ext; unfold pivotMatrix1753 node1753 pivotPermutation1753; decide +kernel
  have hmoment : injectiveMoment H node1753 = injectiveMoment H pivotMatrix1753 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1753 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1753 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1753 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1753 (0 : Fin 4) = raw1328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1753 raw1328; decide +kernel
    rw [heq]
    exact (canonical1328 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1753 (1 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1753 (1 : Fin 4) = raw2473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1753 raw2473; decide +kernel
    rw [heq]
    exact (canonical2473 hH).trans (sound845 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1753 (2 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1753 (2 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1753 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1753 (3 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1753 (3 : Fin 4) = raw2497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1753 raw2497; decide +kernel
    rw [heq]
    exact (canonical2497 hH).trans (sound510 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1753 + (injectiveMoment H (mergeFirst pivotMatrix1753 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1753 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1753 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1753 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1753, value510, value831, value837, value845, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1754 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1754 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem sound1754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1754 = Sparse.eval value1754 (momentVector H) := by
  have heq : pivotMatrix1754 = (fun u v => node1754 (pivotPermutation1754 u) v) := by apply Matrix.ext; unfold pivotMatrix1754 node1754 pivotPermutation1754; decide +kernel
  have hmoment : injectiveMoment H node1754 = injectiveMoment H pivotMatrix1754 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1754 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1754 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1754 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1754 (0 : Fin 4) = raw3447 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1754 raw3447; decide +kernel
    rw [heq]
    exact (canonical3447 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1754 (1 : Fin 4)) =
      Sparse.eval value1125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1754 (1 : Fin 4) = raw2388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1754 raw2388; decide +kernel
    rw [heq]
    exact (canonical2388 hH).trans (sound1125 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1754 (2 : Fin 4)) =
      Sparse.eval value826 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1754 (2 : Fin 4) = raw2229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1754 raw2229; decide +kernel
    rw [heq]
    exact (canonical2229 hH).trans (sound826 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1754 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1754 (3 : Fin 4) = raw2227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1754 raw2227; decide +kernel
    rw [heq]
    exact (canonical2227 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1754 + (injectiveMoment H (mergeFirst pivotMatrix1754 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1754 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1754 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1754 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1754, value1125, value1234, value775, value826, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1755 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1755 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem sound1755 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1755 = Sparse.eval value1755 (momentVector H) := by
  have heq : pivotMatrix1755 = (fun u v => node1755 (pivotPermutation1755 u) v) := by apply Matrix.ext; unfold pivotMatrix1755 node1755 pivotPermutation1755; decide +kernel
  have hmoment : injectiveMoment H node1755 = injectiveMoment H pivotMatrix1755 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1755 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1755 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1755 (0 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1755 (0 : Fin 4) = raw3448 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1755 raw3448; decide +kernel
    rw [heq]
    exact (canonical3448 hH).trans (sound976 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1755 (1 : Fin 4)) =
      Sparse.eval value509 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1755 (1 : Fin 4) = raw2389 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1755 raw2389; decide +kernel
    rw [heq]
    exact (canonical2389 hH).trans (sound509 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1755 (2 : Fin 4)) =
      Sparse.eval value827 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1755 (2 : Fin 4) = raw2230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1755 raw2230; decide +kernel
    rw [heq]
    exact (canonical2230 hH).trans (sound827 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1755 (3 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1755 (3 : Fin 4) = raw2228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1755 raw2228; decide +kernel
    rw [heq]
    exact (canonical2228 hH).trans (sound483 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1755 + (injectiveMoment H (mergeFirst pivotMatrix1755 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1755 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1755 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1755 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1755, value483, value509, value827, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1756 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1756 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem sound1756 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1756 = Sparse.eval value1756 (momentVector H) := by
  have heq : pivotMatrix1756 = (fun u v => node1756 (pivotPermutation1756 u) v) := by apply Matrix.ext; unfold pivotMatrix1756 node1756 pivotPermutation1756; decide +kernel
  have hmoment : injectiveMoment H node1756 = injectiveMoment H pivotMatrix1756 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1756 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1756 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1756 (0 : Fin 4)) =
      Sparse.eval value1281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1756 (0 : Fin 4) = raw3733 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1756 raw3733; decide +kernel
    rw [heq]
    exact (canonical3733 hH).trans (sound1281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1756 (1 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1756 (1 : Fin 4) = raw2397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1756 raw2397; decide +kernel
    rw [heq]
    exact (canonical2397 hH).trans (sound1111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1756 (2 : Fin 4)) =
      Sparse.eval value506 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1756 (2 : Fin 4) = raw2221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1756 raw2221; decide +kernel
    rw [heq]
    exact (canonical2221 hH).trans (sound506 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1756 (3 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1756 (3 : Fin 4) = raw2216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1756 raw2216; decide +kernel
    rw [heq]
    exact (canonical2216 hH).trans (sound832 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1756 + (injectiveMoment H (mergeFirst pivotMatrix1756 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1756 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1756 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1756 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1756, value1111, value1281, value506, value832, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1757 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1757 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem sound1757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1757 = Sparse.eval value1757 (momentVector H) := by
  have heq : pivotMatrix1757 = (fun u v => node1757 (pivotPermutation1757 u) v) := by apply Matrix.ext; unfold pivotMatrix1757 node1757 pivotPermutation1757; decide +kernel
  have hmoment : injectiveMoment H node1757 = injectiveMoment H pivotMatrix1757 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1757 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1757 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1757 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1757 (0 : Fin 4) = raw3734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1757 raw3734; decide +kernel
    rw [heq]
    exact (canonical3734 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1757 (1 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1757 (1 : Fin 4) = raw2399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1757 raw2399; decide +kernel
    rw [heq]
    exact (canonical2399 hH).trans (sound510 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1757 (2 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1757 (2 : Fin 4) = raw2224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1757 raw2224; decide +kernel
    rw [heq]
    exact (canonical2224 hH).trans (sound496 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1757 (3 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1757 (3 : Fin 4) = raw2218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1757 raw2218; decide +kernel
    rw [heq]
    exact (canonical2218 hH).trans (sound831 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1757 + (injectiveMoment H (mergeFirst pivotMatrix1757 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1757 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1757 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1757 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1757, value1010, value496, value510, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1758 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1758 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound1758 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1758 = Sparse.eval value1758 (momentVector H) := by
  have heq : pivotMatrix1758 = (fun u v => node1758 (pivotPermutation1758 u) v) := by apply Matrix.ext; unfold pivotMatrix1758 node1758 pivotPermutation1758; decide +kernel
  have hmoment : injectiveMoment H node1758 = injectiveMoment H pivotMatrix1758 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1758 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1758 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1758 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1758 (0 : Fin 4) = raw3741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1758 raw3741; decide +kernel
    rw [heq]
    exact (canonical3741 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1758 (1 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1758 (1 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1758 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1758 (2 : Fin 4)) =
      Sparse.eval value827 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1758 (2 : Fin 4) = raw2230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1758 raw2230; decide +kernel
    rw [heq]
    exact (canonical2230 hH).trans (sound827 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1758 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1758 (3 : Fin 4) = raw2227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1758 raw2227; decide +kernel
    rw [heq]
    exact (canonical2227 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1758 + (injectiveMoment H (mergeFirst pivotMatrix1758 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1758 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1758 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1758 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1758, value1234, value1249, value827, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1759 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1759 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem sound1759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1759 = Sparse.eval value1759 (momentVector H) := by
  have heq : pivotMatrix1759 = (fun u v => node1759 (pivotPermutation1759 u) v) := by apply Matrix.ext; unfold pivotMatrix1759 node1759 pivotPermutation1759; decide +kernel
  have hmoment : injectiveMoment H node1759 = injectiveMoment H pivotMatrix1759 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1759 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1759 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1759 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1759 (0 : Fin 4) = raw3742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1759 raw3742; decide +kernel
    rw [heq]
    exact (canonical3742 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1759 (1 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1759 (1 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1759 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1759 (2 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1759 (2 : Fin 4) = raw2231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1759 raw2231; decide +kernel
    rw [heq]
    exact (canonical2231 hH).trans (sound828 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1759 (3 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1759 (3 : Fin 4) = raw2228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1759 raw2228; decide +kernel
    rw [heq]
    exact (canonical2228 hH).trans (sound483 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1759 + (injectiveMoment H (mergeFirst pivotMatrix1759 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1759 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1759 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1759 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1759, value1058, value483, value513, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1760 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1760 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem sound1760 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1760 = Sparse.eval value1760 (momentVector H) := by
  have heq : pivotMatrix1760 = (fun u v => node1760 (pivotPermutation1760 u) v) := by apply Matrix.ext; unfold pivotMatrix1760 node1760 pivotPermutation1760; decide +kernel
  have hmoment : injectiveMoment H node1760 = injectiveMoment H pivotMatrix1760 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1760 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1760 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1760 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1760 (0 : Fin 4) = raw5738 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1760 raw5738; decide +kernel
    rw [heq]
    exact (canonical5738 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1760 (1 : Fin 4)) =
      Sparse.eval value518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1760 (1 : Fin 4) = raw2509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1760 raw2509; decide +kernel
    rw [heq]
    exact (canonical2509 hH).trans (sound518 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1760 (2 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1760 (2 : Fin 4) = raw2232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1760 raw2232; decide +kernel
    rw [heq]
    exact (canonical2232 hH).trans (sound828 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1760 (3 : Fin 4)) =
      Sparse.eval value506 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1760 (3 : Fin 4) = raw2221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1760 raw2221; decide +kernel
    rw [heq]
    exact (canonical2221 hH).trans (sound506 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1760 + (injectiveMoment H (mergeFirst pivotMatrix1760 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1760 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1760 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1760 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1760, value506, value518, value828, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1761 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1761 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem sound1761 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1761 = Sparse.eval value1761 (momentVector H) := by
  have heq : pivotMatrix1761 = (fun u v => node1761 (pivotPermutation1761 u) v) := by apply Matrix.ext; unfold pivotMatrix1761 node1761 pivotPermutation1761; decide +kernel
  have hmoment : injectiveMoment H node1761 = injectiveMoment H pivotMatrix1761 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1761 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1761 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1761 (0 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1761 (0 : Fin 4) = raw6637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1761 raw6637; decide +kernel
    rw [heq]
    exact (canonical6637 hH).trans (sound1112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1761 (1 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1761 (1 : Fin 4) = raw2518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1761 raw2518; decide +kernel
    rw [heq]
    exact (canonical2518 hH).trans (sound510 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1761 (2 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1761 (2 : Fin 4) = raw2234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1761 raw2234; decide +kernel
    rw [heq]
    exact (canonical2234 hH).trans (sound483 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1761 (3 : Fin 4)) =
      Sparse.eval value506 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1761 (3 : Fin 4) = raw2221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1761 raw2221; decide +kernel
    rw [heq]
    exact (canonical2221 hH).trans (sound506 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1761 + (injectiveMoment H (mergeFirst pivotMatrix1761 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1761 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1761 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1761 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1761, value1112, value483, value506, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1762 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1762 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem sound1762 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1762 = Sparse.eval value1762 (momentVector H) := by
  have heq : pivotMatrix1762 = (fun u v => node1762 (pivotPermutation1762 u) v) := by apply Matrix.ext; unfold pivotMatrix1762 node1762 pivotPermutation1762; decide +kernel
  have hmoment : injectiveMoment H node1762 = injectiveMoment H pivotMatrix1762 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1762 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1762 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1762 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1762 (0 : Fin 4) = raw6435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1762 raw6435; decide +kernel
    rw [heq]
    exact (canonical6435 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1762 (1 : Fin 4)) =
      Sparse.eval value519 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1762 (1 : Fin 4) = raw2515 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1762 raw2515; decide +kernel
    rw [heq]
    exact (canonical2515 hH).trans (sound519 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1762 (2 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1762 (2 : Fin 4) = raw2234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1762 raw2234; decide +kernel
    rw [heq]
    exact (canonical2234 hH).trans (sound483 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1762 (3 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1762 (3 : Fin 4) = raw2224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1762 raw2224; decide +kernel
    rw [heq]
    exact (canonical2224 hH).trans (sound496 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1762 + (injectiveMoment H (mergeFirst pivotMatrix1762 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1762 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1762 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1762 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1762, value1036, value483, value496, value519, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1763 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1763 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound1763 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1763 = Sparse.eval value1763 (momentVector H) := by
  have heq : pivotMatrix1763 = (fun u v => node1763 (pivotPermutation1763 u) v) := by apply Matrix.ext; unfold pivotMatrix1763 node1763 pivotPermutation1763; decide +kernel
  have hmoment : injectiveMoment H node1763 = injectiveMoment H pivotMatrix1763 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1763 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1763 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1763 (0 : Fin 4)) =
      Sparse.eval value833 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1763 (0 : Fin 4) = raw5740 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1763 raw5740; decide +kernel
    rw [heq]
    exact (canonical5740 hH).trans (sound833 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1763 (1 : Fin 4)) =
      Sparse.eval value821 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1763 (1 : Fin 4) = raw2510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1763 raw2510; decide +kernel
    rw [heq]
    exact (canonical2510 hH).trans (sound821 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1763 (2 : Fin 4)) =
      Sparse.eval value826 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1763 (2 : Fin 4) = raw2233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1763 raw2233; decide +kernel
    rw [heq]
    exact (canonical2233 hH).trans (sound826 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1763 (3 : Fin 4)) =
      Sparse.eval value498 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1763 (3 : Fin 4) = raw2226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1763 raw2226; decide +kernel
    rw [heq]
    exact (canonical2226 hH).trans (sound498 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1763 + (injectiveMoment H (mergeFirst pivotMatrix1763 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1763 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1763 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1763 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1763, value498, value821, value826, value833, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1764 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1764 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem sound1764 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1764 = Sparse.eval value1764 (momentVector H) := by
  have heq : pivotMatrix1764 = (fun u v => node1764 (pivotPermutation1764 u) v) := by apply Matrix.ext; unfold pivotMatrix1764 node1764 pivotPermutation1764; decide +kernel
  have hmoment : injectiveMoment H node1764 = injectiveMoment H pivotMatrix1764 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1764 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1764 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1764 (0 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1764 (0 : Fin 4) = raw1998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1764 raw1998; decide +kernel
    rw [heq]
    exact (canonical1998 hH).trans (sound1306 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1764 (1 : Fin 4)) =
      Sparse.eval value1125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1764 (1 : Fin 4) = raw2388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1764 raw2388; decide +kernel
    rw [heq]
    exact (canonical2388 hH).trans (sound1125 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1764 (2 : Fin 4)) =
      Sparse.eval value512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1764 (2 : Fin 4) = raw2402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1764 raw2402; decide +kernel
    rw [heq]
    exact (canonical2402 hH).trans (sound512 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1764 (3 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1764 (3 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1764 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1764 + (injectiveMoment H (mergeFirst pivotMatrix1764 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1764 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1764 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1764 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1764, value1125, value1249, value1306, value512, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1765 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1765 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem sound1765 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1765 = Sparse.eval value1765 (momentVector H) := by
  have heq : pivotMatrix1765 = (fun u v => node1765 (pivotPermutation1765 u) v) := by apply Matrix.ext; unfold pivotMatrix1765 node1765 pivotPermutation1765; decide +kernel
  have hmoment : injectiveMoment H node1765 = injectiveMoment H pivotMatrix1765 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1765 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1765 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1765 (0 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1765 (0 : Fin 4) = raw2023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1765 raw2023; decide +kernel
    rw [heq]
    exact (canonical2023 hH).trans (sound1028 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1765 (1 : Fin 4)) =
      Sparse.eval value829 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1765 (1 : Fin 4) = raw2393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1765 raw2393; decide +kernel
    rw [heq]
    exact (canonical2393 hH).trans (sound829 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1765 (2 : Fin 4)) =
      Sparse.eval value829 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1765 (2 : Fin 4) = raw2414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1765 raw2414; decide +kernel
    rw [heq]
    exact (canonical2414 hH).trans (sound829 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1765 (3 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1765 (3 : Fin 4) = raw2419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1765 raw2419; decide +kernel
    rw [heq]
    exact (canonical2419 hH).trans (sound1107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1765 + (injectiveMoment H (mergeFirst pivotMatrix1765 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1765 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1765 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1765 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1765, value1028, value1107, value829, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1766 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1766 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem sound1766 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1766 = Sparse.eval value1766 (momentVector H) := by
  have heq : pivotMatrix1766 = (fun u v => node1766 (pivotPermutation1766 u) v) := by apply Matrix.ext; unfold pivotMatrix1766 node1766 pivotPermutation1766; decide +kernel
  have hmoment : injectiveMoment H node1766 = injectiveMoment H pivotMatrix1766 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1766 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1766 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1766 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1766 (0 : Fin 4) = raw2033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1766 raw2033; decide +kernel
    rw [heq]
    exact (canonical2033 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1766 (1 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1766 (1 : Fin 4) = raw2399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1766 raw2399; decide +kernel
    rw [heq]
    exact (canonical2399 hH).trans (sound510 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1766 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1766 (2 : Fin 4) = raw2424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1766 raw2424; decide +kernel
    rw [heq]
    exact (canonical2424 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1766 (3 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1766 (3 : Fin 4) = raw2428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1766 raw2428; decide +kernel
    rw [heq]
    exact (canonical2428 hH).trans (sound1112 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1766 + (injectiveMoment H (mergeFirst pivotMatrix1766 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1766 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1766 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1766 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1766, value1079, value1110, value1112, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1767 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1767 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem sound1767 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1767 = Sparse.eval value1767 (momentVector H) := by
  have heq : pivotMatrix1767 = (fun u v => node1767 (pivotPermutation1767 u) v) := by apply Matrix.ext; unfold pivotMatrix1767 node1767 pivotPermutation1767; decide +kernel
  have hmoment : injectiveMoment H node1767 = injectiveMoment H pivotMatrix1767 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1767 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1767 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1767 (0 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1767 (0 : Fin 4) = raw2042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1767 raw2042; decide +kernel
    rw [heq]
    exact (canonical2042 hH).trans (sound1080 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1767 (1 : Fin 4)) =
      Sparse.eval value512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1767 (1 : Fin 4) = raw2402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1767 raw2402; decide +kernel
    rw [heq]
    exact (canonical2402 hH).trans (sound512 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1767 (2 : Fin 4)) =
      Sparse.eval value849 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1767 (2 : Fin 4) = raw2432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1767 raw2432; decide +kernel
    rw [heq]
    exact (canonical2432 hH).trans (sound849 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1767 (3 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1767 (3 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1767 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1767 + (injectiveMoment H (mergeFirst pivotMatrix1767 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1767 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1767 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1767 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1767, value1080, value1123, value512, value849, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1768 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1768 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound1768 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1768 = Sparse.eval value1768 (momentVector H) := by
  have heq : pivotMatrix1768 = (fun u v => node1768 (pivotPermutation1768 u) v) := by apply Matrix.ext; unfold pivotMatrix1768 node1768 pivotPermutation1768; decide +kernel
  have hmoment : injectiveMoment H node1768 = injectiveMoment H pivotMatrix1768 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1768 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1768 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1768 (0 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1768 (0 : Fin 4) = raw2043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1768 raw2043; decide +kernel
    rw [heq]
    exact (canonical2043 hH).trans (sound1268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1768 (1 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1768 (1 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1768 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1768 (2 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1768 (2 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1768 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1768 (3 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1768 (3 : Fin 4) = raw2434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1768 raw2434; decide +kernel
    rw [heq]
    exact (canonical2434 hH).trans (sound1265 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1768 + (injectiveMoment H (mergeFirst pivotMatrix1768 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1768 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1768 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1768 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1768, value1123, value1249, value1265, value1268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1769 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1769 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem sound1769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1769 = Sparse.eval value1769 (momentVector H) := by
  have heq : pivotMatrix1769 = (fun u v => node1769 (pivotPermutation1769 u) v) := by apply Matrix.ext; unfold pivotMatrix1769 node1769 pivotPermutation1769; decide +kernel
  have hmoment : injectiveMoment H node1769 = injectiveMoment H pivotMatrix1769 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1769 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1769 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1769 (0 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1769 (0 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1769 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1769 (1 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1769 (1 : Fin 4) = raw2428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1769 raw2428; decide +kernel
    rw [heq]
    exact (canonical2428 hH).trans (sound1112 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1769 (2 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1769 (2 : Fin 4) = raw2451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1769 raw2451; decide +kernel
    rw [heq]
    exact (canonical2451 hH).trans (sound1040 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1769 (3 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1769 (3 : Fin 4) = raw2455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1769 raw2455; decide +kernel
    rw [heq]
    exact (canonical2455 hH).trans (sound842 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1769 + (injectiveMoment H (mergeFirst pivotMatrix1769 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1769 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1769 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1769 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1769, value1040, value1112, value805, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1770 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1770 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound1770 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1770 = Sparse.eval value1770 (momentVector H) := by
  have heq : pivotMatrix1770 = (fun u v => node1770 (pivotPermutation1770 u) v) := by apply Matrix.ext; unfold pivotMatrix1770 node1770 pivotPermutation1770; decide +kernel
  have hmoment : injectiveMoment H node1770 = injectiveMoment H pivotMatrix1770 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1770 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1770 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1770 (0 : Fin 4)) =
      Sparse.eval value933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1770 (0 : Fin 4) = raw2068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1770 raw2068; decide +kernel
    rw [heq]
    exact (canonical2068 hH).trans (sound933 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1770 (1 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1770 (1 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1770 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1770 (2 : Fin 4)) =
      Sparse.eval value730 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1770 (2 : Fin 4) = raw2456 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1770 raw2456; decide +kernel
    rw [heq]
    exact (canonical2456 hH).trans (sound730 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1770 (3 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1770 (3 : Fin 4) = raw2457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1770 raw2457; decide +kernel
    rw [heq]
    exact (canonical2457 hH).trans (sound835 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1770 + (injectiveMoment H (mergeFirst pivotMatrix1770 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1770 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1770 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1770 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1770, value1123, value730, value835, value933, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1771 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1771 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound1771 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1771 = Sparse.eval value1771 (momentVector H) := by
  have heq : pivotMatrix1771 = (fun u v => node1771 (pivotPermutation1771 u) v) := by apply Matrix.ext; unfold pivotMatrix1771 node1771 pivotPermutation1771; decide +kernel
  have hmoment : injectiveMoment H node1771 = injectiveMoment H pivotMatrix1771 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1771 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1771 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1771 (0 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1771 (0 : Fin 4) = raw2069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1771 raw2069; decide +kernel
    rw [heq]
    exact (canonical2069 hH).trans (sound936 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1771 (1 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1771 (1 : Fin 4) = raw2435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1771 raw2435; decide +kernel
    rw [heq]
    exact (canonical2435 hH).trans (sound1096 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1771 (2 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1771 (2 : Fin 4) = raw2458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1771 raw2458; decide +kernel
    rw [heq]
    exact (canonical2458 hH).trans (sound1260 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1771 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1771 (3 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1771 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1771 + (injectiveMoment H (mergeFirst pivotMatrix1771 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1771 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1771 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1771 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1771, value1078, value1096, value1260, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1772 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1772 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound1772 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1772 = Sparse.eval value1772 (momentVector H) := by
  have heq : pivotMatrix1772 = (fun u v => node1772 (pivotPermutation1772 u) v) := by apply Matrix.ext; unfold pivotMatrix1772 node1772 pivotPermutation1772; decide +kernel
  have hmoment : injectiveMoment H node1772 = injectiveMoment H pivotMatrix1772 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1772 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1772 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1772 (0 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1772 (0 : Fin 4) = raw2081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1772 raw2081; decide +kernel
    rw [heq]
    exact (canonical2081 hH).trans (sound1081 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1772 (1 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1772 (1 : Fin 4) = raw2458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1772 raw2458; decide +kernel
    rw [heq]
    exact (canonical2458 hH).trans (sound1260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1772 (2 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1772 (2 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1772 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1772 (3 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1772 (3 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1772 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1772 + (injectiveMoment H (mergeFirst pivotMatrix1772 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1772 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1772 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1772 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1772, value1058, value1081, value1260, value514, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1773 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1773 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound1773 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1773 = Sparse.eval value1773 (momentVector H) := by
  have heq : pivotMatrix1773 = (fun u v => node1773 (pivotPermutation1773 u) v) := by apply Matrix.ext; unfold pivotMatrix1773 node1773 pivotPermutation1773; decide +kernel
  have hmoment : injectiveMoment H node1773 = injectiveMoment H pivotMatrix1773 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1773 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1773 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1773 (0 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1773 (0 : Fin 4) = raw2105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1773 raw2105; decide +kernel
    rw [heq]
    exact (canonical2105 hH).trans (sound1003 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1773 (1 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1773 (1 : Fin 4) = raw2485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1773 raw2485; decide +kernel
    rw [heq]
    exact (canonical2485 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1773 (2 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1773 (2 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1773 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1773 (3 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1773 (3 : Fin 4) = raw2490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1773 raw2490; decide +kernel
    rw [heq]
    exact (canonical2490 hH).trans (sound1047 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1773 + (injectiveMoment H (mergeFirst pivotMatrix1773 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1773 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1773 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1773 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1773, value1003, value1010, value1047, value517, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1774 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1774 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound1774 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1774 = Sparse.eval value1774 (momentVector H) := by
  have heq : pivotMatrix1774 = (fun u v => node1774 (pivotPermutation1774 u) v) := by apply Matrix.ext; unfold pivotMatrix1774 node1774 pivotPermutation1774; decide +kernel
  have hmoment : injectiveMoment H node1774 = injectiveMoment H pivotMatrix1774 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1774 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1774 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1774 (0 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1774 (0 : Fin 4) = raw2106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1774 raw2106; decide +kernel
    rw [heq]
    exact (canonical2106 hH).trans (sound939 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1774 (1 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1774 (1 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1774 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1774 (2 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1774 (2 : Fin 4) = raw2490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1774 raw2490; decide +kernel
    rw [heq]
    exact (canonical2490 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1774 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1774 (3 : Fin 4) = raw2491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1774 raw2491; decide +kernel
    rw [heq]
    exact (canonical2491 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1774 + (injectiveMoment H (mergeFirst pivotMatrix1774 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1774 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1774 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1774 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1774, value1005, value1047, value1078, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1775 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1775 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem sound1775 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1775 = Sparse.eval value1775 (momentVector H) := by
  have heq : pivotMatrix1775 = (fun u v => node1775 (pivotPermutation1775 u) v) := by apply Matrix.ext; unfold pivotMatrix1775 node1775 pivotPermutation1775; decide +kernel
  have hmoment : injectiveMoment H node1775 = injectiveMoment H pivotMatrix1775 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1775 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1775 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1775 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1775 (0 : Fin 4) = raw2109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1775 raw2109; decide +kernel
    rw [heq]
    exact (canonical2109 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1775 (1 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1775 (1 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1775 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1775 (2 : Fin 4)) =
      Sparse.eval value518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1775 (2 : Fin 4) = raw2493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1775 raw2493; decide +kernel
    rw [heq]
    exact (canonical2493 hH).trans (sound518 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1775 (3 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1775 (3 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1775 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1775 + (injectiveMoment H (mergeFirst pivotMatrix1775 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1775 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1775 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1775 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1775, value1036, value517, value518, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1776 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1776 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1776 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1776 = Sparse.eval value1776 (momentVector H) := by
  have heq : pivotMatrix1776 = (fun u v => node1776 (pivotPermutation1776 u) v) := by apply Matrix.ext; unfold pivotMatrix1776 node1776 pivotPermutation1776; decide +kernel
  have hmoment : injectiveMoment H node1776 = injectiveMoment H pivotMatrix1776 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1776 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1776 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1776 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1776 (0 : Fin 4) = raw2110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1776 raw2110; decide +kernel
    rw [heq]
    exact (canonical2110 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1776 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1776 (1 : Fin 4) = raw2491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1776 raw2491; decide +kernel
    rw [heq]
    exact (canonical2491 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1776 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1776 (2 : Fin 4) = raw2495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1776 raw2495; decide +kernel
    rw [heq]
    exact (canonical2495 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1776 (3 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1776 (3 : Fin 4) = raw2496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1776 raw2496; decide +kernel
    rw [heq]
    exact (canonical2496 hH).trans (sound510 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1776 + (injectiveMoment H (mergeFirst pivotMatrix1776 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1776 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1776 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1776 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1776, value1053, value1078, value1079, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1777 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1777 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound1777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1777 = Sparse.eval value1777 (momentVector H) := by
  have heq : pivotMatrix1777 = (fun u v => node1777 (pivotPermutation1777 u) v) := by apply Matrix.ext; unfold pivotMatrix1777 node1777 pivotPermutation1777; decide +kernel
  have hmoment : injectiveMoment H node1777 = injectiveMoment H pivotMatrix1777 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1777 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1777 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1777 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1777 (0 : Fin 4) = raw2116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1777 raw2116; decide +kernel
    rw [heq]
    exact (canonical2116 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1777 (1 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1777 (1 : Fin 4) = raw2499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1777 raw2499; decide +kernel
    rw [heq]
    exact (canonical2499 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1777 (2 : Fin 4)) =
      Sparse.eval value821 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1777 (2 : Fin 4) = raw2502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1777 raw2502; decide +kernel
    rw [heq]
    exact (canonical2502 hH).trans (sound821 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1777 (3 : Fin 4)) =
      Sparse.eval value501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1777 (3 : Fin 4) = raw2503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1777 raw2503; decide +kernel
    rw [heq]
    exact (canonical2503 hH).trans (sound501 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1777 + (injectiveMoment H (mergeFirst pivotMatrix1777 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1777 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1777 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1777 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1777, value1013, value501, value821, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1778 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1778 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound1778 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1778 = Sparse.eval value1778 (momentVector H) := by
  have heq : pivotMatrix1778 = (fun u v => node1778 (pivotPermutation1778 u) v) := by apply Matrix.ext; unfold pivotMatrix1778 node1778 pivotPermutation1778; decide +kernel
  have hmoment : injectiveMoment H node1778 = injectiveMoment H pivotMatrix1778 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1778 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1778 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1778 (0 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1778 (0 : Fin 4) = raw2117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1778 raw2117; decide +kernel
    rw [heq]
    exact (canonical2117 hH).trans (sound1155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1778 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1778 (1 : Fin 4) = raw2500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1778 raw2500; decide +kernel
    rw [heq]
    exact (canonical2500 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1778 (2 : Fin 4)) =
      Sparse.eval value501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1778 (2 : Fin 4) = raw2503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1778 raw2503; decide +kernel
    rw [heq]
    exact (canonical2503 hH).trans (sound501 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1778 (3 : Fin 4)) =
      Sparse.eval value1076 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1778 (3 : Fin 4) = raw2504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1778 raw2504; decide +kernel
    rw [heq]
    exact (canonical2504 hH).trans (sound1076 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1778 + (injectiveMoment H (mergeFirst pivotMatrix1778 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1778 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1778 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1778 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1778, value1016, value1076, value1155, value501, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1779 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1779 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound1779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1779 = Sparse.eval value1779 (momentVector H) := by
  have heq : pivotMatrix1779 = (fun u v => node1779 (pivotPermutation1779 u) v) := by apply Matrix.ext; unfold pivotMatrix1779 node1779 pivotPermutation1779; decide +kernel
  have hmoment : injectiveMoment H node1779 = injectiveMoment H pivotMatrix1779 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1779 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1779 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1779 (0 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1779 (0 : Fin 4) = raw2589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1779 raw2589; decide +kernel
    rw [heq]
    exact (canonical2589 hH).trans (sound1018 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1779 (1 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1779 (1 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1779 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1779 (2 : Fin 4)) =
      Sparse.eval value509 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1779 (2 : Fin 4) = raw2389 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1779 raw2389; decide +kernel
    rw [heq]
    exact (canonical2389 hH).trans (sound509 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1779 (3 : Fin 4)) =
      Sparse.eval value1125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1779 (3 : Fin 4) = raw2388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1779 raw2388; decide +kernel
    rw [heq]
    exact (canonical2388 hH).trans (sound1125 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1779 + (injectiveMoment H (mergeFirst pivotMatrix1779 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1779 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1779 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1779 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1779, value1018, value1125, value1249, value509, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1780 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1780 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem sound1780 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1780 = Sparse.eval value1780 (momentVector H) := by
  have heq : pivotMatrix1780 = (fun u v => node1780 (pivotPermutation1780 u) v) := by apply Matrix.ext; unfold pivotMatrix1780 node1780 pivotPermutation1780; decide +kernel
  have hmoment : injectiveMoment H node1780 = injectiveMoment H pivotMatrix1780 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1780 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1780 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1780 (0 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1780 (0 : Fin 4) = raw2591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1780 raw2591; decide +kernel
    rw [heq]
    exact (canonical2591 hH).trans (sound842 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1780 (1 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1780 (1 : Fin 4) = raw2419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1780 raw2419; decide +kernel
    rw [heq]
    exact (canonical2419 hH).trans (sound1107 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1780 (2 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1780 (2 : Fin 4) = raw2397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1780 raw2397; decide +kernel
    rw [heq]
    exact (canonical2397 hH).trans (sound1111 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1780 (3 : Fin 4)) =
      Sparse.eval value829 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1780 (3 : Fin 4) = raw2393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1780 raw2393; decide +kernel
    rw [heq]
    exact (canonical2393 hH).trans (sound829 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1780 + (injectiveMoment H (mergeFirst pivotMatrix1780 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1780 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1780 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1780 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1780, value1107, value1111, value829, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1781 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1781 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem sound1781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1781 = Sparse.eval value1781 (momentVector H) := by
  have heq : pivotMatrix1781 = (fun u v => node1781 (pivotPermutation1781 u) v) := by apply Matrix.ext; unfold pivotMatrix1781 node1781 pivotPermutation1781; decide +kernel
  have hmoment : injectiveMoment H node1781 = injectiveMoment H pivotMatrix1781 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1781 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1781 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1781 (0 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1781 (0 : Fin 4) = raw2594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1781 raw2594; decide +kernel
    rw [heq]
    exact (canonical2594 hH).trans (sound1112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1781 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1781 (1 : Fin 4) = raw2424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1781 raw2424; decide +kernel
    rw [heq]
    exact (canonical2424 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1781 (2 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1781 (2 : Fin 4) = raw2399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1781 raw2399; decide +kernel
    rw [heq]
    exact (canonical2399 hH).trans (sound510 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1781 (3 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1781 (3 : Fin 4) = raw2397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1781 raw2397; decide +kernel
    rw [heq]
    exact (canonical2397 hH).trans (sound1111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1781 + (injectiveMoment H (mergeFirst pivotMatrix1781 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1781 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1781 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1781 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1781, value1110, value1111, value1112, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1782 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1782 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem sound1782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1782 = Sparse.eval value1782 (momentVector H) := by
  have heq : pivotMatrix1782 = (fun u v => node1782 (pivotPermutation1782 u) v) := by apply Matrix.ext; unfold pivotMatrix1782 node1782 pivotPermutation1782; decide +kernel
  have hmoment : injectiveMoment H node1782 = injectiveMoment H pivotMatrix1782 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1782 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1782 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1782 (0 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1782 (0 : Fin 4) = raw2595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1782 raw2595; decide +kernel
    rw [heq]
    exact (canonical2595 hH).trans (sound510 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1782 (1 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1782 (1 : Fin 4) = raw2428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1782 raw2428; decide +kernel
    rw [heq]
    exact (canonical2428 hH).trans (sound1112 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1782 (2 : Fin 4)) =
      Sparse.eval value511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1782 (2 : Fin 4) = raw2401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1782 raw2401; decide +kernel
    rw [heq]
    exact (canonical2401 hH).trans (sound511 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1782 (3 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1782 (3 : Fin 4) = raw2399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1782 raw2399; decide +kernel
    rw [heq]
    exact (canonical2399 hH).trans (sound510 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1782 + (injectiveMoment H (mergeFirst pivotMatrix1782 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1782 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1782 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1782 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1782, value1112, value510, value511, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1783 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1783 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound1783 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1783 = Sparse.eval value1783 (momentVector H) := by
  have heq : pivotMatrix1783 = (fun u v => node1783 (pivotPermutation1783 u) v) := by apply Matrix.ext; unfold pivotMatrix1783 node1783 pivotPermutation1783; decide +kernel
  have hmoment : injectiveMoment H node1783 = injectiveMoment H pivotMatrix1783 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1783 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1783 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1783 (0 : Fin 4)) =
      Sparse.eval value515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1783 (0 : Fin 4) = raw2596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1783 raw2596; decide +kernel
    rw [heq]
    exact (canonical2596 hH).trans (sound515 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1783 (1 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1783 (1 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1783 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1783 (2 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1783 (2 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1783 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1783 (3 : Fin 4)) =
      Sparse.eval value512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1783 (3 : Fin 4) = raw2402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1783 raw2402; decide +kernel
    rw [heq]
    exact (canonical2402 hH).trans (sound512 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1783 + (injectiveMoment H (mergeFirst pivotMatrix1783 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1783 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1783 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1783 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1783, value1123, value1249, value512, value515, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1784 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1784 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound1784 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1784 = Sparse.eval value1784 (momentVector H) := by
  have heq : pivotMatrix1784 = (fun u v => node1784 (pivotPermutation1784 u) v) := by apply Matrix.ext; unfold pivotMatrix1784 node1784 pivotPermutation1784; decide +kernel
  have hmoment : injectiveMoment H node1784 = injectiveMoment H pivotMatrix1784 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1784 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1784 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1784 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (0 : Fin 4) = raw2597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2597; decide +kernel
    rw [heq]
    exact (canonical2597 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1784 (1 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (1 : Fin 4) = raw2434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2434; decide +kernel
    rw [heq]
    exact (canonical2434 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1784 (2 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (2 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1784 (3 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1784 (3 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1784 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1784 + (injectiveMoment H (mergeFirst pivotMatrix1784 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1784 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1784 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1784 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1784, value1058, value1249, value1265, value513, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1785 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1785 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem sound1785 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1785 = Sparse.eval value1785 (momentVector H) := by
  have heq : pivotMatrix1785 = (fun u v => node1785 (pivotPermutation1785 u) v) := by apply Matrix.ext; unfold pivotMatrix1785 node1785 pivotPermutation1785; decide +kernel
  have hmoment : injectiveMoment H node1785 = injectiveMoment H pivotMatrix1785 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1785 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1785 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1785 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1785 (0 : Fin 4) = raw2601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1785 raw2601; decide +kernel
    rw [heq]
    exact (canonical2601 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1785 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1785 (1 : Fin 4) = raw2445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1785 raw2445; decide +kernel
    rw [heq]
    exact (canonical2445 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1785 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1785 (2 : Fin 4) = raw2424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1785 raw2424; decide +kernel
    rw [heq]
    exact (canonical2424 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1785 (3 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1785 (3 : Fin 4) = raw2419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1785 raw2419; decide +kernel
    rw [heq]
    exact (canonical2419 hH).trans (sound1107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1785 + (injectiveMoment H (mergeFirst pivotMatrix1785 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1785 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1785 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1785 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1785, value1040, value1107, value1110, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1786 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1786 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem sound1786 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1786 = Sparse.eval value1786 (momentVector H) := by
  have heq : pivotMatrix1786 = (fun u v => node1786 (pivotPermutation1786 u) v) := by apply Matrix.ext; unfold pivotMatrix1786 node1786 pivotPermutation1786; decide +kernel
  have hmoment : injectiveMoment H node1786 = injectiveMoment H pivotMatrix1786 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1786 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1786 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1786 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1786 (0 : Fin 4) = raw2604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1786 raw2604; decide +kernel
    rw [heq]
    exact (canonical2604 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1786 (1 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1786 (1 : Fin 4) = raw2451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1786 raw2451; decide +kernel
    rw [heq]
    exact (canonical2451 hH).trans (sound1040 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1786 (2 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1786 (2 : Fin 4) = raw2428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1786 raw2428; decide +kernel
    rw [heq]
    exact (canonical2428 hH).trans (sound1112 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1786 (3 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1786 (3 : Fin 4) = raw2424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1786 raw2424; decide +kernel
    rw [heq]
    exact (canonical2424 hH).trans (sound1110 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1786 + (injectiveMoment H (mergeFirst pivotMatrix1786 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1786 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1786 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1786 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1786, value1040, value1110, value1112, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1787 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1787 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

theorem sound1787 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1787 = Sparse.eval value1787 (momentVector H) := by
  have heq : pivotMatrix1787 = (fun u v => node1787 (pivotPermutation1787 u) v) := by apply Matrix.ext; unfold pivotMatrix1787 node1787 pivotPermutation1787; decide +kernel
  have hmoment : injectiveMoment H node1787 = injectiveMoment H pivotMatrix1787 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1787 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1787 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1787 (0 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1787 (0 : Fin 4) = raw2606 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1787 raw2606; decide +kernel
    rw [heq]
    exact (canonical2606 hH).trans (sound1111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1787 (1 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1787 (1 : Fin 4) = raw2455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1787 raw2455; decide +kernel
    rw [heq]
    exact (canonical2455 hH).trans (sound842 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1787 (2 : Fin 4)) =
      Sparse.eval value852 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1787 (2 : Fin 4) = raw2431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1787 raw2431; decide +kernel
    rw [heq]
    exact (canonical2431 hH).trans (sound852 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1787 (3 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1787 (3 : Fin 4) = raw2428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1787 raw2428; decide +kernel
    rw [heq]
    exact (canonical2428 hH).trans (sound1112 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1787 + (injectiveMoment H (mergeFirst pivotMatrix1787 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1787 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1787 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1787 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1787, value1111, value1112, value842, value852, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1788 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1788 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

theorem sound1788 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1788 = Sparse.eval value1788 (momentVector H) := by
  have heq : pivotMatrix1788 = (fun u v => node1788 (pivotPermutation1788 u) v) := by apply Matrix.ext; unfold pivotMatrix1788 node1788 pivotPermutation1788; decide +kernel
  have hmoment : injectiveMoment H node1788 = injectiveMoment H pivotMatrix1788 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1788 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1788 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1788 (0 : Fin 4)) =
      Sparse.eval value851 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1788 (0 : Fin 4) = raw2607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1788 raw2607; decide +kernel
    rw [heq]
    exact (canonical2607 hH).trans (sound851 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1788 (1 : Fin 4)) =
      Sparse.eval value730 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1788 (1 : Fin 4) = raw2456 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1788 raw2456; decide +kernel
    rw [heq]
    exact (canonical2456 hH).trans (sound730 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1788 (2 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1788 (2 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1788 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1788 (3 : Fin 4)) =
      Sparse.eval value849 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1788 (3 : Fin 4) = raw2432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1788 raw2432; decide +kernel
    rw [heq]
    exact (canonical2432 hH).trans (sound849 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1788 + (injectiveMoment H (mergeFirst pivotMatrix1788 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1788 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1788 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1788 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1788, value1123, value730, value849, value851, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1789 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1789 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound1789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1789 = Sparse.eval value1789 (momentVector H) := by
  have heq : pivotMatrix1789 = (fun u v => node1789 (pivotPermutation1789 u) v) := by apply Matrix.ext; unfold pivotMatrix1789 node1789 pivotPermutation1789; decide +kernel
  have hmoment : injectiveMoment H node1789 = injectiveMoment H pivotMatrix1789 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1789 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1789 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1789 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1789 (0 : Fin 4) = raw2608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1789 raw2608; decide +kernel
    rw [heq]
    exact (canonical2608 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1789 (1 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1789 (1 : Fin 4) = raw2457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1789 raw2457; decide +kernel
    rw [heq]
    exact (canonical2457 hH).trans (sound835 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1789 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1789 (2 : Fin 4) = raw2434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1789 raw2434; decide +kernel
    rw [heq]
    exact (canonical2434 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1789 (3 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1789 (3 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1789 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1789 + (injectiveMoment H (mergeFirst pivotMatrix1789 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1789 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1789 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1789 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1789, value1078, value1123, value1265, value835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1790 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1790 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound1790 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1790 = Sparse.eval value1790 (momentVector H) := by
  have heq : pivotMatrix1790 = (fun u v => node1790 (pivotPermutation1790 u) v) := by apply Matrix.ext; unfold pivotMatrix1790 node1790 pivotPermutation1790; decide +kernel
  have hmoment : injectiveMoment H node1790 = injectiveMoment H pivotMatrix1790 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1790 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1790 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1790 (0 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1790 (0 : Fin 4) = raw2609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1790 raw2609; decide +kernel
    rw [heq]
    exact (canonical2609 hH).trans (sound1260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1790 (1 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1790 (1 : Fin 4) = raw2458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1790 raw2458; decide +kernel
    rw [heq]
    exact (canonical2458 hH).trans (sound1260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1790 (2 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1790 (2 : Fin 4) = raw2435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1790 raw2435; decide +kernel
    rw [heq]
    exact (canonical2435 hH).trans (sound1096 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1790 (3 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1790 (3 : Fin 4) = raw2434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1790 raw2434; decide +kernel
    rw [heq]
    exact (canonical2434 hH).trans (sound1265 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1790 + (injectiveMoment H (mergeFirst pivotMatrix1790 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1790 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1790 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1790 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1790, value1096, value1260, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1791 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1791 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem sound1791 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1791 = Sparse.eval value1791 (momentVector H) := by
  have heq : pivotMatrix1791 = (fun u v => node1791 (pivotPermutation1791 u) v) := by apply Matrix.ext; unfold pivotMatrix1791 node1791 pivotPermutation1791; decide +kernel
  have hmoment : injectiveMoment H node1791 = injectiveMoment H pivotMatrix1791 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1791 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1791 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1791 (0 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1791 (0 : Fin 4) = raw2616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1791 raw2616; decide +kernel
    rw [heq]
    exact (canonical2616 hH).trans (sound1107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1791 (1 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1791 (1 : Fin 4) = raw2469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1791 raw2469; decide +kernel
    rw [heq]
    exact (canonical2469 hH).trans (sound842 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1791 (2 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1791 (2 : Fin 4) = raw2455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1791 raw2455; decide +kernel
    rw [heq]
    exact (canonical2455 hH).trans (sound842 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1791 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1791 (3 : Fin 4) = raw2451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1791 raw2451; decide +kernel
    rw [heq]
    exact (canonical2451 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1791 + (injectiveMoment H (mergeFirst pivotMatrix1791 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1791 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1791 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1791 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1791, value1040, value1107, value842, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
