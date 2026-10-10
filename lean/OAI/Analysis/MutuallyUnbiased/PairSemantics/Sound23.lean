import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1472 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1472 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem sound1472 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1472 = Sparse.eval value1472 (momentVector H) := by
  have heq : pivotMatrix1472 = (fun u v => node1472 (pivotPermutation1472 u) v) := by apply Matrix.ext; unfold pivotMatrix1472 node1472 pivotPermutation1472; decide +kernel
  have hmoment : injectiveMoment H node1472 = injectiveMoment H pivotMatrix1472 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1472 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1472 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1472 (0 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1472 (0 : Fin 4) = raw1262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1472 raw1262; decide +kernel
    rw [heq]
    exact (canonical1262 hH).trans (sound815 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1472 (1 : Fin 4)) =
      Sparse.eval value404 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1472 (1 : Fin 4) = raw1153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1472 raw1153; decide +kernel
    rw [heq]
    exact (canonical1153 hH).trans (sound404 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1472 (2 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1472 (2 : Fin 4) = raw1144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1472 raw1144; decide +kernel
    rw [heq]
    exact (canonical1144 hH).trans (sound997 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1472 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1472 (3 : Fin 4) = raw1143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1472 raw1143; decide +kernel
    rw [heq]
    exact (canonical1143 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1472 + (injectiveMoment H (mergeFirst pivotMatrix1472 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1472 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1472 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1472 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1472, value404, value786, value815, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1473 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1473 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

theorem sound1473 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1473 = Sparse.eval value1473 (momentVector H) := by
  have heq : pivotMatrix1473 = (fun u v => node1473 (pivotPermutation1473 u) v) := by apply Matrix.ext; unfold pivotMatrix1473 node1473 pivotPermutation1473; decide +kernel
  have hmoment : injectiveMoment H node1473 = injectiveMoment H pivotMatrix1473 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1473 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1473 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1473 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1473 (0 : Fin 4) = raw1949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1473 raw1949; decide +kernel
    rw [heq]
    exact (canonical1949 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1473 (1 : Fin 4)) =
      Sparse.eval value401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1473 (1 : Fin 4) = raw1155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1473 raw1155; decide +kernel
    rw [heq]
    exact (canonical1155 hH).trans (sound401 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1473 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1473 (2 : Fin 4) = raw1094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1473 raw1094; decide +kernel
    rw [heq]
    exact (canonical1094 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1473 (3 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1473 (3 : Fin 4) = raw1082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1473 raw1082; decide +kernel
    rw [heq]
    exact (canonical1082 hH).trans (sound394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1473 + (injectiveMoment H (mergeFirst pivotMatrix1473 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1473 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1473 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1473 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1473, value394, value395, value401, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1474 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1474 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem sound1474 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1474 = Sparse.eval value1474 (momentVector H) := by
  have heq : pivotMatrix1474 = (fun u v => node1474 (pivotPermutation1474 u) v) := by apply Matrix.ext; unfold pivotMatrix1474 node1474 pivotPermutation1474; decide +kernel
  have hmoment : injectiveMoment H node1474 = injectiveMoment H pivotMatrix1474 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1474 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1474 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1474 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1474 (0 : Fin 4) = raw5687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1474 raw5687; decide +kernel
    rw [heq]
    exact (canonical5687 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1474 (1 : Fin 4)) =
      Sparse.eval value403 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1474 (1 : Fin 4) = raw1166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1474 raw1166; decide +kernel
    rw [heq]
    exact (canonical1166 hH).trans (sound403 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1474 (2 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1474 (2 : Fin 4) = raw1101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1474 raw1101; decide +kernel
    rw [heq]
    exact (canonical1101 hH).trans (sound397 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1474 (3 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1474 (3 : Fin 4) = raw1082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1474 raw1082; decide +kernel
    rw [heq]
    exact (canonical1082 hH).trans (sound394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1474 + (injectiveMoment H (mergeFirst pivotMatrix1474 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1474 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1474 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1474 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1474, value394, value397, value403, value804, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1475 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1475 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound1475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1475 = Sparse.eval value1475 (momentVector H) := by
  have heq : pivotMatrix1475 = (fun u v => node1475 (pivotPermutation1475 u) v) := by apply Matrix.ext; unfold pivotMatrix1475 node1475 pivotPermutation1475; decide +kernel
  have hmoment : injectiveMoment H node1475 = injectiveMoment H pivotMatrix1475 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1475 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1475 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1475 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (0 : Fin 4) = raw1621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1621; decide +kernel
    rw [heq]
    exact (canonical1621 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1475 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (1 : Fin 4) = raw1147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1147; decide +kernel
    rw [heq]
    exact (canonical1147 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1475 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (2 : Fin 4) = raw1094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1094; decide +kernel
    rw [heq]
    exact (canonical1094 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1475 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (3 : Fin 4) = raw1088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1088; decide +kernel
    rw [heq]
    exact (canonical1088 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1475 + (injectiveMoment H (mergeFirst pivotMatrix1475 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1475 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1475 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1475 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1475, value1037, value1257, value395, value775, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1476 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1476 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1476 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1476 = Sparse.eval value1476 (momentVector H) := by
  have heq : pivotMatrix1476 = (fun u v => node1476 (pivotPermutation1476 u) v) := by apply Matrix.ext; unfold pivotMatrix1476 node1476 pivotPermutation1476; decide +kernel
  have hmoment : injectiveMoment H node1476 = injectiveMoment H pivotMatrix1476 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1476 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1476 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1476 (0 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1476 (0 : Fin 4) = raw1627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1476 raw1627; decide +kernel
    rw [heq]
    exact (canonical1627 hH).trans (sound774 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1476 (1 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1476 (1 : Fin 4) = raw1149 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1476 raw1149; decide +kernel
    rw [heq]
    exact (canonical1149 hH).trans (sound771 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1476 (2 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1476 (2 : Fin 4) = raw1096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1476 raw1096; decide +kernel
    rw [heq]
    exact (canonical1096 hH).trans (sound396 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1476 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1476 (3 : Fin 4) = raw1092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1476 raw1092; decide +kernel
    rw [heq]
    exact (canonical1092 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1476 + (injectiveMoment H (mergeFirst pivotMatrix1476 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1476 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1476 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1476 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1476, value396, value771, value773, value774, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1477 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1477 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound1477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1477 = Sparse.eval value1477 (momentVector H) := by
  have heq : pivotMatrix1477 = (fun u v => node1477 (pivotPermutation1477 u) v) := by apply Matrix.ext; unfold pivotMatrix1477 node1477 pivotPermutation1477; decide +kernel
  have hmoment : injectiveMoment H node1477 = injectiveMoment H pivotMatrix1477 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1477 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1477 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1477 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (0 : Fin 4) = raw1641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1641; decide +kernel
    rw [heq]
    exact (canonical1641 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1477 (1 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (1 : Fin 4) = raw1151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1151; decide +kernel
    rw [heq]
    exact (canonical1151 hH).trans (sound998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1477 (2 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (2 : Fin 4) = raw1101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1101; decide +kernel
    rw [heq]
    exact (canonical1101 hH).trans (sound397 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1477 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (3 : Fin 4) = raw1099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1099; decide +kernel
    rw [heq]
    exact (canonical1099 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1477 + (injectiveMoment H (mergeFirst pivotMatrix1477 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1477 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1477 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1477 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1477, value1257, value397, value771, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1478 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1478 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1478 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1478 = Sparse.eval value1478 (momentVector H) := by
  have heq : pivotMatrix1478 = (fun u v => node1478 (pivotPermutation1478 u) v) := by apply Matrix.ext; unfold pivotMatrix1478 node1478 pivotPermutation1478; decide +kernel
  have hmoment : injectiveMoment H node1478 = injectiveMoment H pivotMatrix1478 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1478 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1478 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1478 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1478 (0 : Fin 4) = raw1642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1478 raw1642; decide +kernel
    rw [heq]
    exact (canonical1642 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1478 (1 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1478 (1 : Fin 4) = raw1152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1478 raw1152; decide +kernel
    rw [heq]
    exact (canonical1152 hH).trans (sound786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1478 (2 : Fin 4)) =
      Sparse.eval value398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1478 (2 : Fin 4) = raw1102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1478 raw1102; decide +kernel
    rw [heq]
    exact (canonical1102 hH).trans (sound398 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1478 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1478 (3 : Fin 4) = raw1100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1478 raw1100; decide +kernel
    rw [heq]
    exact (canonical1100 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1478 + (injectiveMoment H (mergeFirst pivotMatrix1478 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1478 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1478 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1478 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1478, value398, value769, value773, value786, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1479 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1479 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound1479 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1479 = Sparse.eval value1479 (momentVector H) := by
  have heq : pivotMatrix1479 = (fun u v => node1479 (pivotPermutation1479 u) v) := by apply Matrix.ext; unfold pivotMatrix1479 node1479 pivotPermutation1479; decide +kernel
  have hmoment : injectiveMoment H node1479 = injectiveMoment H pivotMatrix1479 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1479 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1479 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1479 (0 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1479 (0 : Fin 4) = raw1964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1479 raw1964; decide +kernel
    rw [heq]
    exact (canonical1964 hH).trans (sound806 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1479 (1 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1479 (1 : Fin 4) = raw1156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1479 raw1156; decide +kernel
    rw [heq]
    exact (canonical1156 hH).trans (sound1164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1479 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1479 (2 : Fin 4) = raw1098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1479 raw1098; decide +kernel
    rw [heq]
    exact (canonical1098 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1479 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1479 (3 : Fin 4) = raw1092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1479 raw1092; decide +kernel
    rw [heq]
    exact (canonical1092 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1479 + (injectiveMoment H (mergeFirst pivotMatrix1479 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1479 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1479 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1479 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1479, value1164, value395, value773, value806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1480 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1480 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound1480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1480 = Sparse.eval value1480 (momentVector H) := by
  have heq : pivotMatrix1480 = (fun u v => node1480 (pivotPermutation1480 u) v) := by apply Matrix.ext; unfold pivotMatrix1480 node1480 pivotPermutation1480; decide +kernel
  have hmoment : injectiveMoment H node1480 = injectiveMoment H pivotMatrix1480 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1480 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1480 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1480 (0 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1480 (0 : Fin 4) = raw1979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1480 raw1979; decide +kernel
    rw [heq]
    exact (canonical1979 hH).trans (sound802 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1480 (1 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1480 (1 : Fin 4) = raw1158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1480 raw1158; decide +kernel
    rw [heq]
    exact (canonical1158 hH).trans (sound997 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1480 (2 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1480 (2 : Fin 4) = raw1103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1480 raw1103; decide +kernel
    rw [heq]
    exact (canonical1103 hH).trans (sound397 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1480 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1480 (3 : Fin 4) = raw1100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1480 raw1100; decide +kernel
    rw [heq]
    exact (canonical1100 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1480 + (injectiveMoment H (mergeFirst pivotMatrix1480 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1480 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1480 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1480 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1480, value397, value773, value802, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1481 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1481 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound1481 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1481 = Sparse.eval value1481 (momentVector H) := by
  have heq : pivotMatrix1481 = (fun u v => node1481 (pivotPermutation1481 u) v) := by apply Matrix.ext; unfold pivotMatrix1481 node1481 pivotPermutation1481; decide +kernel
  have hmoment : injectiveMoment H node1481 = injectiveMoment H pivotMatrix1481 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1481 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1481 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1481 (0 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1481 (0 : Fin 4) = raw5702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1481 raw5702; decide +kernel
    rw [heq]
    exact (canonical5702 hH).trans (sound815 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1481 (1 : Fin 4)) =
      Sparse.eval value404 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1481 (1 : Fin 4) = raw1167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1481 raw1167; decide +kernel
    rw [heq]
    exact (canonical1167 hH).trans (sound404 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1481 (2 : Fin 4)) =
      Sparse.eval value402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1481 (2 : Fin 4) = raw1113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1481 raw1113; decide +kernel
    rw [heq]
    exact (canonical1113 hH).trans (sound402 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1481 (3 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1481 (3 : Fin 4) = raw1107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1481 raw1107; decide +kernel
    rw [heq]
    exact (canonical1107 hH).trans (sound400 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1481 + (injectiveMoment H (mergeFirst pivotMatrix1481 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1481 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1481 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1481 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1481, value400, value402, value404, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1482 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1482 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound1482 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1482 = Sparse.eval value1482 (momentVector H) := by
  have heq : pivotMatrix1482 = (fun u v => node1482 (pivotPermutation1482 u) v) := by apply Matrix.ext; unfold pivotMatrix1482 node1482 pivotPermutation1482; decide +kernel
  have hmoment : injectiveMoment H node1482 = injectiveMoment H pivotMatrix1482 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1482 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1482 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1482 (0 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1482 (0 : Fin 4) = raw5703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1482 raw5703; decide +kernel
    rw [heq]
    exact (canonical5703 hH).trans (sound816 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1482 (1 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1482 (1 : Fin 4) = raw1168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1482 raw1168; decide +kernel
    rw [heq]
    exact (canonical1168 hH).trans (sound997 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1482 (2 : Fin 4)) =
      Sparse.eval value1238 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1482 (2 : Fin 4) = raw1114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1482 raw1114; decide +kernel
    rw [heq]
    exact (canonical1114 hH).trans (sound1238 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1482 (3 : Fin 4)) =
      Sparse.eval value401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1482 (3 : Fin 4) = raw1109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1482 raw1109; decide +kernel
    rw [heq]
    exact (canonical1109 hH).trans (sound401 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1482 + (injectiveMoment H (mergeFirst pivotMatrix1482 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1482 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1482 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1482 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1482, value1238, value401, value816, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1483 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1483 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem sound1483 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1483 = Sparse.eval value1483 (momentVector H) := by
  have heq : pivotMatrix1483 = (fun u v => node1483 (pivotPermutation1483 u) v) := by apply Matrix.ext; unfold pivotMatrix1483 node1483 pivotPermutation1483; decide +kernel
  have hmoment : injectiveMoment H node1483 = injectiveMoment H pivotMatrix1483 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1483 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1483 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1483 (0 : Fin 4)) =
      Sparse.eval value981 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1483 (0 : Fin 4) = raw1667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1483 raw1667; decide +kernel
    rw [heq]
    exact (canonical1667 hH).trans (sound981 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1483 (1 : Fin 4)) =
      Sparse.eval value814 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1483 (1 : Fin 4) = raw1159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1483 raw1159; decide +kernel
    rw [heq]
    exact (canonical1159 hH).trans (sound814 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1483 (2 : Fin 4)) =
      Sparse.eval value813 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1483 (2 : Fin 4) = raw1132 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1483 raw1132; decide +kernel
    rw [heq]
    exact (canonical1132 hH).trans (sound813 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1483 (3 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1483 (3 : Fin 4) = raw1128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1483 raw1128; decide +kernel
    rw [heq]
    exact (canonical1128 hH).trans (sound1070 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1483 + (injectiveMoment H (mergeFirst pivotMatrix1483 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1483 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1483 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1483 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1483, value1070, value813, value814, value981, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1484 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1484 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

theorem sound1484 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1484 = Sparse.eval value1484 (momentVector H) := by
  have heq : pivotMatrix1484 = (fun u v => node1484 (pivotPermutation1484 u) v) := by apply Matrix.ext; unfold pivotMatrix1484 node1484 pivotPermutation1484; decide +kernel
  have hmoment : injectiveMoment H node1484 = injectiveMoment H pivotMatrix1484 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1484 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1484 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1484 (0 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1484 (0 : Fin 4) = raw1668 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1484 raw1668; decide +kernel
    rw [heq]
    exact (canonical1668 hH).trans (sound1170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1484 (1 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1484 (1 : Fin 4) = raw1160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1484 raw1160; decide +kernel
    rw [heq]
    exact (canonical1160 hH).trans (sound1164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1484 (2 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1484 (2 : Fin 4) = raw1133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1484 raw1133; decide +kernel
    rw [heq]
    exact (canonical1133 hH).trans (sound996 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1484 (3 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1484 (3 : Fin 4) = raw1129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1484 raw1129; decide +kernel
    rw [heq]
    exact (canonical1129 hH).trans (sound1168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1484 + (injectiveMoment H (mergeFirst pivotMatrix1484 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1484 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1484 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1484 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1484, value1164, value1168, value1170, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1485 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1485 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

theorem sound1485 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1485 = Sparse.eval value1485 (momentVector H) := by
  have heq : pivotMatrix1485 = (fun u v => node1485 (pivotPermutation1485 u) v) := by apply Matrix.ext; unfold pivotMatrix1485 node1485 pivotPermutation1485; decide +kernel
  have hmoment : injectiveMoment H node1485 = injectiveMoment H pivotMatrix1485 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1485 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1485 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1485 (0 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1485 (0 : Fin 4) = raw1669 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1485 raw1669; decide +kernel
    rw [heq]
    exact (canonical1669 hH).trans (sound787 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1485 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1485 (1 : Fin 4) = raw1161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1485 raw1161; decide +kernel
    rw [heq]
    exact (canonical1161 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1485 (2 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1485 (2 : Fin 4) = raw1134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1485 raw1134; decide +kernel
    rw [heq]
    exact (canonical1134 hH).trans (sound998 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1485 (3 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1485 (3 : Fin 4) = raw1130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1485 raw1130; decide +kernel
    rw [heq]
    exact (canonical1130 hH).trans (sound998 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1485 + (injectiveMoment H (mergeFirst pivotMatrix1485 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1485 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1485 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1485 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1485, value397, value787, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1486 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1486 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem sound1486 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1486 = Sparse.eval value1486 (momentVector H) := by
  have heq : pivotMatrix1486 = (fun u v => node1486 (pivotPermutation1486 u) v) := by apply Matrix.ext; unfold pivotMatrix1486 node1486 pivotPermutation1486; decide +kernel
  have hmoment : injectiveMoment H node1486 = injectiveMoment H pivotMatrix1486 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1486 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1486 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1486 (0 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1486 (0 : Fin 4) = raw1691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1486 raw1691; decide +kernel
    rw [heq]
    exact (canonical1691 hH).trans (sound1171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1486 (1 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1486 (1 : Fin 4) = raw1162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1486 raw1162; decide +kernel
    rw [heq]
    exact (canonical1162 hH).trans (sound1155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1486 (2 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1486 (2 : Fin 4) = raw1145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1486 raw1145; decide +kernel
    rw [heq]
    exact (canonical1145 hH).trans (sound997 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1486 (3 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1486 (3 : Fin 4) = raw1142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1486 raw1142; decide +kernel
    rw [heq]
    exact (canonical1142 hH).trans (sound1168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1486 + (injectiveMoment H (mergeFirst pivotMatrix1486 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1486 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1486 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1486 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1486, value1155, value1168, value1171, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1487 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1487 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound1487 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1487 = Sparse.eval value1487 (momentVector H) := by
  have heq : pivotMatrix1487 = (fun u v => node1487 (pivotPermutation1487 u) v) := by apply Matrix.ext; unfold pivotMatrix1487 node1487 pivotPermutation1487; decide +kernel
  have hmoment : injectiveMoment H node1487 = injectiveMoment H pivotMatrix1487 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1487 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1487 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1487 (0 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1487 (0 : Fin 4) = raw1702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1487 raw1702; decide +kernel
    rw [heq]
    exact (canonical1702 hH).trans (sound786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1487 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1487 (1 : Fin 4) = raw1164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1487 raw1164; decide +kernel
    rw [heq]
    exact (canonical1164 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1487 (2 : Fin 4)) =
      Sparse.eval value404 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1487 (2 : Fin 4) = raw1154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1487 raw1154; decide +kernel
    rw [heq]
    exact (canonical1154 hH).trans (sound404 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1487 (3 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1487 (3 : Fin 4) = raw1151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1487 raw1151; decide +kernel
    rw [heq]
    exact (canonical1151 hH).trans (sound998 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1487 + (injectiveMoment H (mergeFirst pivotMatrix1487 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1487 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1487 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1487 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1487, value1037, value404, value786, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1488 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1488 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 0, -3]]

theorem sound1488 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1488 = Sparse.eval value1488 (momentVector H) := by
  have heq : pivotMatrix1488 = (fun u v => node1488 (pivotPermutation1488 u) v) := by apply Matrix.ext; unfold pivotMatrix1488 node1488 pivotPermutation1488; decide +kernel
  have hmoment : injectiveMoment H node1488 = injectiveMoment H pivotMatrix1488 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1488 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1488 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1488 (0 : Fin 4)) =
      Sparse.eval value1255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1488 (0 : Fin 4) = raw1278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1488 raw1278; decide +kernel
    rw [heq]
    exact (canonical1278 hH).trans (sound1255 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1488 (1 : Fin 4)) =
      Sparse.eval value1252 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1488 (1 : Fin 4) = raw1189 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1488 raw1189; decide +kernel
    rw [heq]
    exact (canonical1189 hH).trans (sound1252 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1488 (2 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1488 (2 : Fin 4) = raw1174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1488 raw1174; decide +kernel
    rw [heq]
    exact (canonical1174 hH).trans (sound405 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1488 (3 : Fin 4)) =
      Sparse.eval value1254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1488 (3 : Fin 4) = raw1172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1488 raw1172; decide +kernel
    rw [heq]
    exact (canonical1172 hH).trans (sound1254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1488 + (injectiveMoment H (mergeFirst pivotMatrix1488 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1488 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1488 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1488 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1488, value1252, value1254, value1255, value405, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1489 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1489 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem sound1489 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1489 = Sparse.eval value1489 (momentVector H) := by
  have heq : pivotMatrix1489 = (fun u v => node1489 (pivotPermutation1489 u) v) := by apply Matrix.ext; unfold pivotMatrix1489 node1489 pivotPermutation1489; decide +kernel
  have hmoment : injectiveMoment H node1489 = injectiveMoment H pivotMatrix1489 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1489 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1489 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1489 (0 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1489 (0 : Fin 4) = raw2216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1489 raw2216; decide +kernel
    rw [heq]
    exact (canonical2216 hH).trans (sound832 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1489 (1 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1489 (1 : Fin 4) = raw1231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1489 raw1231; decide +kernel
    rw [heq]
    exact (canonical1231 hH).trans (sound1035 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1489 (2 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1489 (2 : Fin 4) = raw1175 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1489 raw1175; decide +kernel
    rw [heq]
    exact (canonical1175 hH).trans (sound406 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1489 (3 : Fin 4)) =
      Sparse.eval value1254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1489 (3 : Fin 4) = raw1172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1489 raw1172; decide +kernel
    rw [heq]
    exact (canonical1172 hH).trans (sound1254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1489 + (injectiveMoment H (mergeFirst pivotMatrix1489 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1489 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1489 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1489 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1489, value1035, value1254, value406, value832, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1490 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1490 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound1490 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1490 = Sparse.eval value1490 (momentVector H) := by
  have heq : pivotMatrix1490 = (fun u v => node1490 (pivotPermutation1490 u) v) := by apply Matrix.ext; unfold pivotMatrix1490 node1490 pivotPermutation1490; decide +kernel
  have hmoment : injectiveMoment H node1490 = injectiveMoment H pivotMatrix1490 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1490 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1490 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1490 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1490 (0 : Fin 4) = raw2218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1490 raw2218; decide +kernel
    rw [heq]
    exact (canonical2218 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1490 (1 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1490 (1 : Fin 4) = raw1233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1490 raw1233; decide +kernel
    rw [heq]
    exact (canonical1233 hH).trans (sound408 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1490 (2 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1490 (2 : Fin 4) = raw1176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1490 raw1176; decide +kernel
    rw [heq]
    exact (canonical1176 hH).trans (sound406 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1490 (3 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1490 (3 : Fin 4) = raw1174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1490 raw1174; decide +kernel
    rw [heq]
    exact (canonical1174 hH).trans (sound405 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1490 + (injectiveMoment H (mergeFirst pivotMatrix1490 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1490 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1490 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1490 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1490, value405, value406, value408, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1491 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1491 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem sound1491 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1491 = Sparse.eval value1491 (momentVector H) := by
  have heq : pivotMatrix1491 = (fun u v => node1491 (pivotPermutation1491 u) v) := by apply Matrix.ext; unfold pivotMatrix1491 node1491 pivotPermutation1491; decide +kernel
  have hmoment : injectiveMoment H node1491 = injectiveMoment H pivotMatrix1491 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1491 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1491 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1491 (0 : Fin 4)) =
      Sparse.eval value795 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1491 (0 : Fin 4) = raw1034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1491 raw1034; decide +kernel
    rw [heq]
    exact (canonical1034 hH).trans (sound795 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1491 (1 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1491 (1 : Fin 4) = raw1175 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1491 raw1175; decide +kernel
    rw [heq]
    exact (canonical1175 hH).trans (sound406 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1491 (2 : Fin 4)) =
      Sparse.eval value1120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1491 (2 : Fin 4) = raw1193 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1491 raw1193; decide +kernel
    rw [heq]
    exact (canonical1193 hH).trans (sound1120 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1491 (3 : Fin 4)) =
      Sparse.eval value1285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1491 (3 : Fin 4) = raw1195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1491 raw1195; decide +kernel
    rw [heq]
    exact (canonical1195 hH).trans (sound1285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1491 + (injectiveMoment H (mergeFirst pivotMatrix1491 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1491 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1491 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1491 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1491, value1120, value1285, value406, value795, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1492 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1492 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem sound1492 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1492 = Sparse.eval value1492 (momentVector H) := by
  have heq : pivotMatrix1492 = (fun u v => node1492 (pivotPermutation1492 u) v) := by apply Matrix.ext; unfold pivotMatrix1492 node1492 pivotPermutation1492; decide +kernel
  have hmoment : injectiveMoment H node1492 = injectiveMoment H pivotMatrix1492 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1492 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1492 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1492 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1492 (0 : Fin 4) = raw1058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1492 raw1058; decide +kernel
    rw [heq]
    exact (canonical1058 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1492 (1 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1492 (1 : Fin 4) = raw1201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1492 raw1201; decide +kernel
    rw [heq]
    exact (canonical1201 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1492 (2 : Fin 4)) =
      Sparse.eval value1329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1492 (2 : Fin 4) = raw1206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1492 raw1206; decide +kernel
    rw [heq]
    exact (canonical1206 hH).trans (sound1329 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1492 (3 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1492 (3 : Fin 4) = raw1211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1492 raw1211; decide +kernel
    rw [heq]
    exact (canonical1211 hH).trans (sound1222 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1492 + (injectiveMoment H (mergeFirst pivotMatrix1492 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1492 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1492 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1492 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1492, value1178, value1222, value1329, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1493 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1493 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem sound1493 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1493 = Sparse.eval value1493 (momentVector H) := by
  have heq : pivotMatrix1493 = (fun u v => node1493 (pivotPermutation1493 u) v) := by apply Matrix.ext; unfold pivotMatrix1493 node1493 pivotPermutation1493; decide +kernel
  have hmoment : injectiveMoment H node1493 = injectiveMoment H pivotMatrix1493 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1493 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1493 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1493 (0 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1493 (0 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1493 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1493 (1 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1493 (1 : Fin 4) = raw1203 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1493 raw1203; decide +kernel
    rw [heq]
    exact (canonical1203 hH).trans (sound268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1493 (2 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1493 (2 : Fin 4) = raw1211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1493 raw1211; decide +kernel
    rw [heq]
    exact (canonical1211 hH).trans (sound1222 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1493 (3 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1493 (3 : Fin 4) = raw1216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1493 raw1216; decide +kernel
    rw [heq]
    exact (canonical1216 hH).trans (sound973 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1493 + (injectiveMoment H (mergeFirst pivotMatrix1493 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1493 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1493 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1493 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1493, value1222, value268, value914, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1494 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem sound1494 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1494 = Sparse.eval value1494 (momentVector H) := by
  have heq : pivotMatrix1494 = (fun u v => node1494 (pivotPermutation1494 u) v) := by apply Matrix.ext; unfold pivotMatrix1494 node1494 pivotPermutation1494; decide +kernel
  have hmoment : injectiveMoment H node1494 = injectiveMoment H pivotMatrix1494 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1494 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1494 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1494 (0 : Fin 4)) =
      Sparse.eval value1029 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1494 (0 : Fin 4) = raw1118 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1494 raw1118; decide +kernel
    rw [heq]
    exact (canonical1118 hH).trans (sound1029 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1494 (1 : Fin 4)) =
      Sparse.eval value830 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1494 (1 : Fin 4) = raw1228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1494 raw1228; decide +kernel
    rw [heq]
    exact (canonical1228 hH).trans (sound830 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1494 (2 : Fin 4)) =
      Sparse.eval value830 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1494 (2 : Fin 4) = raw1239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1494 raw1239; decide +kernel
    rw [heq]
    exact (canonical1239 hH).trans (sound830 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1494 (3 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1494 (3 : Fin 4) = raw1242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1494 raw1242; decide +kernel
    rw [heq]
    exact (canonical1242 hH).trans (sound1028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1494 + (injectiveMoment H (mergeFirst pivotMatrix1494 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1494 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1494 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1494 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1494, value1028, value1029, value830, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1495 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem sound1495 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1495 = Sparse.eval value1495 (momentVector H) := by
  have heq : pivotMatrix1495 = (fun u v => node1495 (pivotPermutation1495 u) v) := by apply Matrix.ext; unfold pivotMatrix1495 node1495 pivotPermutation1495; decide +kernel
  have hmoment : injectiveMoment H node1495 = injectiveMoment H pivotMatrix1495 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1495 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1495 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1495 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1495 (0 : Fin 4) = raw1121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1495 raw1121; decide +kernel
    rw [heq]
    exact (canonical1121 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1495 (1 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1495 (1 : Fin 4) = raw1231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1495 raw1231; decide +kernel
    rw [heq]
    exact (canonical1231 hH).trans (sound1035 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1495 (2 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1495 (2 : Fin 4) = raw1242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1495 raw1242; decide +kernel
    rw [heq]
    exact (canonical1242 hH).trans (sound1028 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1495 (3 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1495 (3 : Fin 4) = raw1245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1495 raw1245; decide +kernel
    rw [heq]
    exact (canonical1245 hH).trans (sound1032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1495 + (injectiveMoment H (mergeFirst pivotMatrix1495 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1495 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1495 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1495 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1495, value1028, value1031, value1032, value1035, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1496 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1496 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound1496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1496 = Sparse.eval value1496 (momentVector H) := by
  have heq : pivotMatrix1496 = (fun u v => node1496 (pivotPermutation1496 u) v) := by apply Matrix.ext; unfold pivotMatrix1496 node1496 pivotPermutation1496; decide +kernel
  have hmoment : injectiveMoment H node1496 = injectiveMoment H pivotMatrix1496 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1496 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1496 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1496 (0 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1496 (0 : Fin 4) = raw1124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1496 raw1124; decide +kernel
    rw [heq]
    exact (canonical1124 hH).trans (sound1037 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1496 (1 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1496 (1 : Fin 4) = raw1233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1496 raw1233; decide +kernel
    rw [heq]
    exact (canonical1233 hH).trans (sound408 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1496 (2 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1496 (2 : Fin 4) = raw1245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1496 raw1245; decide +kernel
    rw [heq]
    exact (canonical1245 hH).trans (sound1032 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1496 (3 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1496 (3 : Fin 4) = raw1248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1496 raw1248; decide +kernel
    rw [heq]
    exact (canonical1248 hH).trans (sound1036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1496 + (injectiveMoment H (mergeFirst pivotMatrix1496 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1496 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1496 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1496 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1496, value1032, value1036, value1037, value408, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1497 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1497 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound1497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1497 = Sparse.eval value1497 (momentVector H) := by
  have heq : pivotMatrix1497 = (fun u v => node1497 (pivotPermutation1497 u) v) := by apply Matrix.ext; unfold pivotMatrix1497 node1497 pivotPermutation1497; decide +kernel
  have hmoment : injectiveMoment H node1497 = injectiveMoment H pivotMatrix1497 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1497 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1497 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1497 (0 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1497 (0 : Fin 4) = raw1128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1497 raw1128; decide +kernel
    rw [heq]
    exact (canonical1128 hH).trans (sound1070 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1497 (1 : Fin 4)) =
      Sparse.eval value848 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1497 (1 : Fin 4) = raw1234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1497 raw1234; decide +kernel
    rw [heq]
    exact (canonical1234 hH).trans (sound848 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1497 (2 : Fin 4)) =
      Sparse.eval value848 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1497 (2 : Fin 4) = raw1249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1497 raw1249; decide +kernel
    rw [heq]
    exact (canonical1249 hH).trans (sound848 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1497 (3 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1497 (3 : Fin 4) = raw1250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1497 raw1250; decide +kernel
    rw [heq]
    exact (canonical1250 hH).trans (sound1104 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1497 + (injectiveMoment H (mergeFirst pivotMatrix1497 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1497 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1497 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1497 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1497, value1070, value1104, value848, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1498 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1498 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem sound1498 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1498 = Sparse.eval value1498 (momentVector H) := by
  have heq : pivotMatrix1498 = (fun u v => node1498 (pivotPermutation1498 u) v) := by apply Matrix.ext; unfold pivotMatrix1498 node1498 pivotPermutation1498; decide +kernel
  have hmoment : injectiveMoment H node1498 = injectiveMoment H pivotMatrix1498 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1498 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1498 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1498 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1498 (0 : Fin 4) = raw1129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1498 raw1129; decide +kernel
    rw [heq]
    exact (canonical1129 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1498 (1 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1498 (1 : Fin 4) = raw1235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1498 raw1235; decide +kernel
    rw [heq]
    exact (canonical1235 hH).trans (sound1239 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1498 (2 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1498 (2 : Fin 4) = raw1250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1498 raw1250; decide +kernel
    rw [heq]
    exact (canonical1250 hH).trans (sound1104 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1498 (3 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1498 (3 : Fin 4) = raw1251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1498 raw1251; decide +kernel
    rw [heq]
    exact (canonical1251 hH).trans (sound1198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1498 + (injectiveMoment H (mergeFirst pivotMatrix1498 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1498 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1498 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1498 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1498, value1104, value1168, value1198, value1239, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1499 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1499 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1499 = Sparse.eval value1499 (momentVector H) := by
  have heq : pivotMatrix1499 = (fun u v => node1499 (pivotPermutation1499 u) v) := by apply Matrix.ext; unfold pivotMatrix1499 node1499 pivotPermutation1499; decide +kernel
  have hmoment : injectiveMoment H node1499 = injectiveMoment H pivotMatrix1499 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1499 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1499 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1499 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1499 (0 : Fin 4) = raw1139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1499 raw1139; decide +kernel
    rw [heq]
    exact (canonical1139 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1499 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1499 (1 : Fin 4) = raw1248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1499 raw1248; decide +kernel
    rw [heq]
    exact (canonical1248 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1499 (2 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1499 (2 : Fin 4) = raw1257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1499 raw1257; decide +kernel
    rw [heq]
    exact (canonical1257 hH).trans (sound959 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1499 (3 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1499 (3 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1499 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1499 + (injectiveMoment H (mergeFirst pivotMatrix1499 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1499 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1499 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1499 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1499, value1036, value771, value804, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1500 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1500 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound1500 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1500 = Sparse.eval value1500 (momentVector H) := by
  have heq : pivotMatrix1500 = (fun u v => node1500 (pivotPermutation1500 u) v) := by apply Matrix.ext; unfold pivotMatrix1500 node1500 pivotPermutation1500; decide +kernel
  have hmoment : injectiveMoment H node1500 = injectiveMoment H pivotMatrix1500 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1500 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1500 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1500 (0 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1500 (0 : Fin 4) = raw1143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1500 raw1143; decide +kernel
    rw [heq]
    exact (canonical1143 hH).trans (sound786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1500 (1 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1500 (1 : Fin 4) = raw1252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1500 raw1252; decide +kernel
    rw [heq]
    exact (canonical1252 hH).trans (sound995 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1500 (2 : Fin 4)) =
      Sparse.eval value964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1500 (2 : Fin 4) = raw1261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1500 raw1261; decide +kernel
    rw [heq]
    exact (canonical1261 hH).trans (sound964 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1500 (3 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1500 (3 : Fin 4) = raw1262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1500 raw1262; decide +kernel
    rw [heq]
    exact (canonical1262 hH).trans (sound815 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1500 + (injectiveMoment H (mergeFirst pivotMatrix1500 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1500 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1500 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1500 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1500, value786, value815, value964, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1501 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1501 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound1501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1501 = Sparse.eval value1501 (momentVector H) := by
  have heq : pivotMatrix1501 = (fun u v => node1501 (pivotPermutation1501 u) v) := by apply Matrix.ext; unfold pivotMatrix1501 node1501 pivotPermutation1501; decide +kernel
  have hmoment : injectiveMoment H node1501 = injectiveMoment H pivotMatrix1501 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1501 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1501 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1501 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1501 (0 : Fin 4) = raw1304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1501 raw1304; decide +kernel
    rw [heq]
    exact (canonical1304 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1501 (1 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1501 (1 : Fin 4) = raw1245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1501 raw1245; decide +kernel
    rw [heq]
    exact (canonical1245 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1501 (2 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1501 (2 : Fin 4) = raw1233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1501 raw1233; decide +kernel
    rw [heq]
    exact (canonical1233 hH).trans (sound408 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1501 (3 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1501 (3 : Fin 4) = raw1231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1501 raw1231; decide +kernel
    rw [heq]
    exact (canonical1231 hH).trans (sound1035 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1501 + (injectiveMoment H (mergeFirst pivotMatrix1501 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1501 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1501 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1501 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1501, value1032, value1035, value408, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1502 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1502 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1502 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1502 = Sparse.eval value1502 (momentVector H) := by
  have heq : pivotMatrix1502 = (fun u v => node1502 (pivotPermutation1502 u) v) := by apply Matrix.ext; unfold pivotMatrix1502 node1502 pivotPermutation1502; decide +kernel
  have hmoment : injectiveMoment H node1502 = injectiveMoment H pivotMatrix1502 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1502 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1502 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1502 (0 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1502 (0 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1502 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1502 (1 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1502 (1 : Fin 4) = raw1251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1502 raw1251; decide +kernel
    rw [heq]
    exact (canonical1251 hH).trans (sound1198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1502 (2 : Fin 4)) =
      Sparse.eval value409 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1502 (2 : Fin 4) = raw1236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1502 raw1236; decide +kernel
    rw [heq]
    exact (canonical1236 hH).trans (sound409 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1502 (3 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1502 (3 : Fin 4) = raw1235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1502 raw1235; decide +kernel
    rw [heq]
    exact (canonical1235 hH).trans (sound1239 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1502 + (injectiveMoment H (mergeFirst pivotMatrix1502 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1502 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1502 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1502 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1502, value1198, value1239, value409, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1503 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1503 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound1503 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1503 = Sparse.eval value1503 (momentVector H) := by
  have heq : pivotMatrix1503 = (fun u v => node1503 (pivotPermutation1503 u) v) := by apply Matrix.ext; unfold pivotMatrix1503 node1503 pivotPermutation1503; decide +kernel
  have hmoment : injectiveMoment H node1503 = injectiveMoment H pivotMatrix1503 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1503 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1503 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1503 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1503 (0 : Fin 4) = raw1309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1503 raw1309; decide +kernel
    rw [heq]
    exact (canonical1309 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1503 (1 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1503 (1 : Fin 4) = raw1255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1503 raw1255; decide +kernel
    rw [heq]
    exact (canonical1255 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1503 (2 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1503 (2 : Fin 4) = raw1245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1503 raw1245; decide +kernel
    rw [heq]
    exact (canonical1245 hH).trans (sound1032 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1503 (3 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1503 (3 : Fin 4) = raw1242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1503 raw1242; decide +kernel
    rw [heq]
    exact (canonical1242 hH).trans (sound1028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1503 + (injectiveMoment H (mergeFirst pivotMatrix1503 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1503 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1503 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1503 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1503, value1027, value1028, value1032, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1504 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1504 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1504 = Sparse.eval value1504 (momentVector H) := by
  have heq : pivotMatrix1504 = (fun u v => node1504 (pivotPermutation1504 u) v) := by apply Matrix.ext; unfold pivotMatrix1504 node1504 pivotPermutation1504; decide +kernel
  have hmoment : injectiveMoment H node1504 = injectiveMoment H pivotMatrix1504 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1504 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1504 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1504 (0 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1504 (0 : Fin 4) = raw1312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1504 raw1312; decide +kernel
    rw [heq]
    exact (canonical1312 hH).trans (sound1033 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1504 (1 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1504 (1 : Fin 4) = raw1257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1504 raw1257; decide +kernel
    rw [heq]
    exact (canonical1257 hH).trans (sound959 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1504 (2 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1504 (2 : Fin 4) = raw1248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1504 raw1248; decide +kernel
    rw [heq]
    exact (canonical1248 hH).trans (sound1036 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1504 (3 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1504 (3 : Fin 4) = raw1245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1504 raw1245; decide +kernel
    rw [heq]
    exact (canonical1245 hH).trans (sound1032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1504 + (injectiveMoment H (mergeFirst pivotMatrix1504 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1504 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1504 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1504 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1504, value1032, value1033, value1036, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1505 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1505 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound1505 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1505 = Sparse.eval value1505 (momentVector H) := by
  have heq : pivotMatrix1505 = (fun u v => node1505 (pivotPermutation1505 u) v) := by apply Matrix.ext; unfold pivotMatrix1505 node1505 pivotPermutation1505; decide +kernel
  have hmoment : injectiveMoment H node1505 = injectiveMoment H pivotMatrix1505 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1505 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1505 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1505 (0 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1505 (0 : Fin 4) = raw1314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1505 raw1314; decide +kernel
    rw [heq]
    exact (canonical1314 hH).trans (sound1033 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1505 (1 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1505 (1 : Fin 4) = raw1260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1505 raw1260; decide +kernel
    rw [heq]
    exact (canonical1260 hH).trans (sound1198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1505 (2 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1505 (2 : Fin 4) = raw1251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1505 raw1251; decide +kernel
    rw [heq]
    exact (canonical1251 hH).trans (sound1198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1505 (3 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1505 (3 : Fin 4) = raw1250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1505 raw1250; decide +kernel
    rw [heq]
    exact (canonical1250 hH).trans (sound1104 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1505 + (injectiveMoment H (mergeFirst pivotMatrix1505 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1505 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1505 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1505 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1505, value1033, value1104, value1198, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1506 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1506 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1506 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1506 = Sparse.eval value1506 (momentVector H) := by
  have heq : pivotMatrix1506 = (fun u v => node1506 (pivotPermutation1506 u) v) := by apply Matrix.ext; unfold pivotMatrix1506 node1506 pivotPermutation1506; decide +kernel
  have hmoment : injectiveMoment H node1506 = injectiveMoment H pivotMatrix1506 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1506 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1506 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1506 (0 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1506 (0 : Fin 4) = raw1315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1506 raw1315; decide +kernel
    rw [heq]
    exact (canonical1315 hH).trans (sound1237 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1506 (1 : Fin 4)) =
      Sparse.eval value964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1506 (1 : Fin 4) = raw1261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1506 raw1261; decide +kernel
    rw [heq]
    exact (canonical1261 hH).trans (sound964 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1506 (2 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1506 (2 : Fin 4) = raw1252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1506 raw1252; decide +kernel
    rw [heq]
    exact (canonical1252 hH).trans (sound995 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1506 (3 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1506 (3 : Fin 4) = raw1251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1506 raw1251; decide +kernel
    rw [heq]
    exact (canonical1251 hH).trans (sound1198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1506 + (injectiveMoment H (mergeFirst pivotMatrix1506 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1506 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1506 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1506 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1506, value1198, value1237, value964, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1507 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1507 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound1507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1507 = Sparse.eval value1507 (momentVector H) := by
  have heq : pivotMatrix1507 = (fun u v => node1507 (pivotPermutation1507 u) v) := by apply Matrix.ext; unfold pivotMatrix1507 node1507 pivotPermutation1507; decide +kernel
  have hmoment : injectiveMoment H node1507 = injectiveMoment H pivotMatrix1507 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1507 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1507 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1507 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (0 : Fin 4) = raw1320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1320; decide +kernel
    rw [heq]
    exact (canonical1320 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1507 (1 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (1 : Fin 4) = raw1265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1265; decide +kernel
    rw [heq]
    exact (canonical1265 hH).trans (sound804 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1507 (2 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (2 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1507 (3 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1507 (3 : Fin 4) = raw1257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1507 raw1257; decide +kernel
    rw [heq]
    exact (canonical1257 hH).trans (sound959 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1507 + (injectiveMoment H (mergeFirst pivotMatrix1507 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1507 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1507 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1507 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1507, value1027, value804, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1508 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1508 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound1508 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1508 = Sparse.eval value1508 (momentVector H) := by
  have heq : pivotMatrix1508 = (fun u v => node1508 (pivotPermutation1508 u) v) := by apply Matrix.ext; unfold pivotMatrix1508 node1508 pivotPermutation1508; decide +kernel
  have hmoment : injectiveMoment H node1508 = injectiveMoment H pivotMatrix1508 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1508 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1508 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1508 (0 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1508 (0 : Fin 4) = raw1323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1508 raw1323; decide +kernel
    rw [heq]
    exact (canonical1323 hH).trans (sound1033 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1508 (1 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1508 (1 : Fin 4) = raw1267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1508 raw1267; decide +kernel
    rw [heq]
    exact (canonical1267 hH).trans (sound815 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1508 (2 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1508 (2 : Fin 4) = raw1262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1508 raw1262; decide +kernel
    rw [heq]
    exact (canonical1262 hH).trans (sound815 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1508 (3 : Fin 4)) =
      Sparse.eval value964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1508 (3 : Fin 4) = raw1261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1508 raw1261; decide +kernel
    rw [heq]
    exact (canonical1261 hH).trans (sound964 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1508 + (injectiveMoment H (mergeFirst pivotMatrix1508 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1508 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1508 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1508 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1508, value1033, value815, value964, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1509 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1509 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

theorem sound1509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1509 = Sparse.eval value1509 (momentVector H) := by
  have heq : pivotMatrix1509 = (fun u v => node1509 (pivotPermutation1509 u) v) := by apply Matrix.ext; unfold pivotMatrix1509 node1509 pivotPermutation1509; decide +kernel
  have hmoment : injectiveMoment H node1509 = injectiveMoment H pivotMatrix1509 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1509 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1509 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1509 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1509 (0 : Fin 4) = raw1958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1509 raw1958; decide +kernel
    rw [heq]
    exact (canonical1958 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1509 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1509 (1 : Fin 4) = raw1264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1509 raw1264; decide +kernel
    rw [heq]
    exact (canonical1264 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1509 (2 : Fin 4)) =
      Sparse.eval value482 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1509 (2 : Fin 4) = raw1227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1509 raw1227; decide +kernel
    rw [heq]
    exact (canonical1227 hH).trans (sound482 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1509 (3 : Fin 4)) =
      Sparse.eval value1256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1509 (3 : Fin 4) = raw1226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1509 raw1226; decide +kernel
    rw [heq]
    exact (canonical1226 hH).trans (sound1256 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1509 + (injectiveMoment H (mergeFirst pivotMatrix1509 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1509 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1509 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1509 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1509, value1036, value1256, value482, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1510 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1510 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound1510 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1510 = Sparse.eval value1510 (momentVector H) := by
  have heq : pivotMatrix1510 = (fun u v => node1510 (pivotPermutation1510 u) v) := by apply Matrix.ext; unfold pivotMatrix1510 node1510 pivotPermutation1510; decide +kernel
  have hmoment : injectiveMoment H node1510 = injectiveMoment H pivotMatrix1510 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1510 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1510 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1510 (0 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1510 (0 : Fin 4) = raw2406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1510 raw2406; decide +kernel
    rw [heq]
    exact (canonical2406 hH).trans (sound838 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1510 (1 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1510 (1 : Fin 4) = raw1268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1510 raw1268; decide +kernel
    rw [heq]
    exact (canonical1268 hH).trans (sound804 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1510 (2 : Fin 4)) =
      Sparse.eval value409 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1510 (2 : Fin 4) = raw1237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1510 raw1237; decide +kernel
    rw [heq]
    exact (canonical1237 hH).trans (sound409 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1510 (3 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1510 (3 : Fin 4) = raw1235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1510 raw1235; decide +kernel
    rw [heq]
    exact (canonical1235 hH).trans (sound1239 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1510 + (injectiveMoment H (mergeFirst pivotMatrix1510 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1510 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1510 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1510 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1510, value1239, value409, value804, value838, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1511 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1511 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound1511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1511 = Sparse.eval value1511 (momentVector H) := by
  have heq : pivotMatrix1511 = (fun u v => node1511 (pivotPermutation1511 u) v) := by apply Matrix.ext; unfold pivotMatrix1511 node1511 pivotPermutation1511; decide +kernel
  have hmoment : injectiveMoment H node1511 = injectiveMoment H pivotMatrix1511 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1511 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1511 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1511 (0 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1511 (0 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1511 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1511 (1 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1511 (1 : Fin 4) = raw1271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1511 raw1271; decide +kernel
    rw [heq]
    exact (canonical1271 hH).trans (sound815 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1511 (2 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1511 (2 : Fin 4) = raw1238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1511 raw1238; decide +kernel
    rw [heq]
    exact (canonical1238 hH).trans (sound1239 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1511 (3 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1511 (3 : Fin 4) = raw1233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1511 raw1233; decide +kernel
    rw [heq]
    exact (canonical1233 hH).trans (sound408 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1511 + (injectiveMoment H (mergeFirst pivotMatrix1511 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1511 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1511 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1511 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1511, value1239, value408, value815, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1512 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1512 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound1512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1512 = Sparse.eval value1512 (momentVector H) := by
  have heq : pivotMatrix1512 = (fun u v => node1512 (pivotPermutation1512 u) v) := by apply Matrix.ext; unfold pivotMatrix1512 node1512 pivotPermutation1512; decide +kernel
  have hmoment : injectiveMoment H node1512 = injectiveMoment H pivotMatrix1512 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1512 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1512 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1512 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1512 (0 : Fin 4) = raw2049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1512 raw2049; decide +kernel
    rw [heq]
    exact (canonical2049 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1512 (1 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1512 (1 : Fin 4) = raw1268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1512 raw1268; decide +kernel
    rw [heq]
    exact (canonical1268 hH).trans (sound804 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1512 (2 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1512 (2 : Fin 4) = raw1253 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1512 raw1253; decide +kernel
    rw [heq]
    exact (canonical1253 hH).trans (sound995 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1512 (3 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1512 (3 : Fin 4) = raw1251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1512 raw1251; decide +kernel
    rw [heq]
    exact (canonical1251 hH).trans (sound1198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1512 + (injectiveMoment H (mergeFirst pivotMatrix1512 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1512 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1512 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1512 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1512, value1198, value1202, value804, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1513 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1513 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound1513 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1513 = Sparse.eval value1513 (momentVector H) := by
  have heq : pivotMatrix1513 = (fun u v => node1513 (pivotPermutation1513 u) v) := by apply Matrix.ext; unfold pivotMatrix1513 node1513 pivotPermutation1513; decide +kernel
  have hmoment : injectiveMoment H node1513 = injectiveMoment H pivotMatrix1513 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1513 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1513 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1513 (0 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1513 (0 : Fin 4) = raw2071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1513 raw2071; decide +kernel
    rw [heq]
    exact (canonical2071 hH).trans (sound1203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1513 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1513 (1 : Fin 4) = raw1269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1513 raw1269; decide +kernel
    rw [heq]
    exact (canonical1269 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1513 (2 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1513 (2 : Fin 4) = raw1263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1513 raw1263; decide +kernel
    rw [heq]
    exact (canonical1263 hH).trans (sound815 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1513 (3 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1513 (3 : Fin 4) = raw1260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1513 raw1260; decide +kernel
    rw [heq]
    exact (canonical1260 hH).trans (sound1198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1513 + (injectiveMoment H (mergeFirst pivotMatrix1513 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1513 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1513 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1513 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1513, value1036, value1198, value1203, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1514 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1514 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound1514 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1514 = Sparse.eval value1514 (momentVector H) := by
  have heq : pivotMatrix1514 = (fun u v => node1514 (pivotPermutation1514 u) v) := by apply Matrix.ext; unfold pivotMatrix1514 node1514 pivotPermutation1514; decide +kernel
  have hmoment : injectiveMoment H node1514 = injectiveMoment H pivotMatrix1514 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1514 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1514 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1514 (0 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1514 (0 : Fin 4) = raw2555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1514 raw2555; decide +kernel
    rw [heq]
    exact (canonical2555 hH).trans (sound854 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1514 (1 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1514 (1 : Fin 4) = raw1304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1514 raw1304; decide +kernel
    rw [heq]
    exact (canonical1304 hH).trans (sound831 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1514 (2 : Fin 4)) =
      Sparse.eval value412 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1514 (2 : Fin 4) = raw1282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1514 raw1282; decide +kernel
    rw [heq]
    exact (canonical1282 hH).trans (sound412 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1514 (3 : Fin 4)) =
      Sparse.eval value1255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1514 (3 : Fin 4) = raw1278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1514 raw1278; decide +kernel
    rw [heq]
    exact (canonical1278 hH).trans (sound1255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1514 + (injectiveMoment H (mergeFirst pivotMatrix1514 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1514 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1514 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1514 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1514, value1255, value412, value831, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1515 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1515 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1515 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1515 = Sparse.eval value1515 (momentVector H) := by
  have heq : pivotMatrix1515 = (fun u v => node1515 (pivotPermutation1515 u) v) := by apply Matrix.ext; unfold pivotMatrix1515 node1515 pivotPermutation1515; decide +kernel
  have hmoment : injectiveMoment H node1515 = injectiveMoment H pivotMatrix1515 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1515 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1515 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1515 (0 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1515 (0 : Fin 4) = raw2556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1515 raw2556; decide +kernel
    rw [heq]
    exact (canonical2556 hH).trans (sound844 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1515 (1 : Fin 4)) =
      Sparse.eval value518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1515 (1 : Fin 4) = raw1305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1515 raw1305; decide +kernel
    rw [heq]
    exact (canonical1305 hH).trans (sound518 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1515 (2 : Fin 4)) =
      Sparse.eval value411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1515 (2 : Fin 4) = raw1283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1515 raw1283; decide +kernel
    rw [heq]
    exact (canonical1283 hH).trans (sound411 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1515 (3 : Fin 4)) =
      Sparse.eval value410 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1515 (3 : Fin 4) = raw1280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1515 raw1280; decide +kernel
    rw [heq]
    exact (canonical1280 hH).trans (sound410 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1515 + (injectiveMoment H (mergeFirst pivotMatrix1515 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1515 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1515 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1515 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1515, value410, value411, value518, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1516 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1516 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1516 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1516 = Sparse.eval value1516 (momentVector H) := by
  have heq : pivotMatrix1516 = (fun u v => node1516 (pivotPermutation1516 u) v) := by apply Matrix.ext; unfold pivotMatrix1516 node1516 pivotPermutation1516; decide +kernel
  have hmoment : injectiveMoment H node1516 = injectiveMoment H pivotMatrix1516 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1516 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1516 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1516 (0 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1516 (0 : Fin 4) = raw2561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1516 raw2561; decide +kernel
    rw [heq]
    exact (canonical2561 hH).trans (sound853 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1516 (1 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1516 (1 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1516 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1516 (2 : Fin 4)) =
      Sparse.eval value413 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1516 (2 : Fin 4) = raw1285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1516 raw1285; decide +kernel
    rw [heq]
    exact (canonical1285 hH).trans (sound413 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1516 (3 : Fin 4)) =
      Sparse.eval value1255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1516 (3 : Fin 4) = raw1284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1516 raw1284; decide +kernel
    rw [heq]
    exact (canonical1284 hH).trans (sound1255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1516 + (injectiveMoment H (mergeFirst pivotMatrix1516 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1516 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1516 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1516 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1516, value1255, value413, value828, value853, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1517 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1517 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem sound1517 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1517 = Sparse.eval value1517 (momentVector H) := by
  have heq : pivotMatrix1517 = (fun u v => node1517 (pivotPermutation1517 u) v) := by apply Matrix.ext; unfold pivotMatrix1517 node1517 pivotPermutation1517; decide +kernel
  have hmoment : injectiveMoment H node1517 = injectiveMoment H pivotMatrix1517 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1517 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1517 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1517 (0 : Fin 4)) =
      Sparse.eval value1285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1517 (0 : Fin 4) = raw1195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1517 raw1195; decide +kernel
    rw [heq]
    exact (canonical1195 hH).trans (sound1285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1517 (1 : Fin 4)) =
      Sparse.eval value412 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1517 (1 : Fin 4) = raw1282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1517 raw1282; decide +kernel
    rw [heq]
    exact (canonical1282 hH).trans (sound412 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1517 (2 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1517 (2 : Fin 4) = raw1292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1517 raw1292; decide +kernel
    rw [heq]
    exact (canonical1292 hH).trans (sound1059 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1517 (3 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1517 (3 : Fin 4) = raw1294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1517 raw1294; decide +kernel
    rw [heq]
    exact (canonical1294 hH).trans (sound1059 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1517 + (injectiveMoment H (mergeFirst pivotMatrix1517 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1517 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1517 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1517 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1517, value1059, value1285, value412, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1518 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1518 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound1518 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1518 = Sparse.eval value1518 (momentVector H) := by
  have heq : pivotMatrix1518 = (fun u v => node1518 (pivotPermutation1518 u) v) := by apply Matrix.ext; unfold pivotMatrix1518 node1518 pivotPermutation1518; decide +kernel
  have hmoment : injectiveMoment H node1518 = injectiveMoment H pivotMatrix1518 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1518 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1518 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1518 (0 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1518 (0 : Fin 4) = raw1245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1518 raw1245; decide +kernel
    rw [heq]
    exact (canonical1245 hH).trans (sound1032 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1518 (1 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1518 (1 : Fin 4) = raw1304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1518 raw1304; decide +kernel
    rw [heq]
    exact (canonical1304 hH).trans (sound831 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1518 (2 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1518 (2 : Fin 4) = raw1309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1518 raw1309; decide +kernel
    rw [heq]
    exact (canonical1309 hH).trans (sound1027 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1518 (3 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1518 (3 : Fin 4) = raw1312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1518 raw1312; decide +kernel
    rw [heq]
    exact (canonical1312 hH).trans (sound1033 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1518 + (injectiveMoment H (mergeFirst pivotMatrix1518 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1518 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1518 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1518 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1518, value1027, value1032, value1033, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1519 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1519 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1519 = Sparse.eval value1519 (momentVector H) := by
  have heq : pivotMatrix1519 = (fun u v => node1519 (pivotPermutation1519 u) v) := by apply Matrix.ext; unfold pivotMatrix1519 node1519 pivotPermutation1519; decide +kernel
  have hmoment : injectiveMoment H node1519 = injectiveMoment H pivotMatrix1519 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1519 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1519 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1519 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1519 (0 : Fin 4) = raw1248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1519 raw1248; decide +kernel
    rw [heq]
    exact (canonical1248 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1519 (1 : Fin 4)) =
      Sparse.eval value518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1519 (1 : Fin 4) = raw1305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1519 raw1305; decide +kernel
    rw [heq]
    exact (canonical1305 hH).trans (sound518 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1519 (2 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1519 (2 : Fin 4) = raw1312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1519 raw1312; decide +kernel
    rw [heq]
    exact (canonical1312 hH).trans (sound1033 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1519 (3 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1519 (3 : Fin 4) = raw1313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1519 raw1313; decide +kernel
    rw [heq]
    exact (canonical1313 hH).trans (sound831 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1519 + (injectiveMoment H (mergeFirst pivotMatrix1519 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1519 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1519 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1519 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1519, value1033, value1036, value518, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1520 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1520 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1520 = Sparse.eval value1520 (momentVector H) := by
  have heq : pivotMatrix1520 = (fun u v => node1520 (pivotPermutation1520 u) v) := by apply Matrix.ext; unfold pivotMatrix1520 node1520 pivotPermutation1520; decide +kernel
  have hmoment : injectiveMoment H node1520 = injectiveMoment H pivotMatrix1520 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1520 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1520 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1520 (0 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1520 (0 : Fin 4) = raw1251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1520 raw1251; decide +kernel
    rw [heq]
    exact (canonical1251 hH).trans (sound1198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1520 (1 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1520 (1 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1520 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1520 (2 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1520 (2 : Fin 4) = raw1314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1520 raw1314; decide +kernel
    rw [heq]
    exact (canonical1314 hH).trans (sound1033 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1520 (3 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1520 (3 : Fin 4) = raw1315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1520 raw1315; decide +kernel
    rw [heq]
    exact (canonical1315 hH).trans (sound1237 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1520 + (injectiveMoment H (mergeFirst pivotMatrix1520 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1520 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1520 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1520 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1520, value1033, value1198, value1237, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1521 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1521 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1521 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1521 = Sparse.eval value1521 (momentVector H) := by
  have heq : pivotMatrix1521 = (fun u v => node1521 (pivotPermutation1521 u) v) := by apply Matrix.ext; unfold pivotMatrix1521 node1521 pivotPermutation1521; decide +kernel
  have hmoment : injectiveMoment H node1521 = injectiveMoment H pivotMatrix1521 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1521 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1521 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1521 (0 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1521 (0 : Fin 4) = raw1257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1521 raw1257; decide +kernel
    rw [heq]
    exact (canonical1257 hH).trans (sound959 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1521 (1 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1521 (1 : Fin 4) = raw1312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1521 raw1312; decide +kernel
    rw [heq]
    exact (canonical1312 hH).trans (sound1033 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1521 (2 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1521 (2 : Fin 4) = raw1317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1521 raw1317; decide +kernel
    rw [heq]
    exact (canonical1317 hH).trans (sound1033 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1521 (3 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1521 (3 : Fin 4) = raw1320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1521 raw1320; decide +kernel
    rw [heq]
    exact (canonical1320 hH).trans (sound1027 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1521 + (injectiveMoment H (mergeFirst pivotMatrix1521 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1521 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1521 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1521 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1521, value1027, value1033, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1522 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1522 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem sound1522 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1522 = Sparse.eval value1522 (momentVector H) := by
  have heq : pivotMatrix1522 = (fun u v => node1522 (pivotPermutation1522 u) v) := by apply Matrix.ext; unfold pivotMatrix1522 node1522 pivotPermutation1522; decide +kernel
  have hmoment : injectiveMoment H node1522 = injectiveMoment H pivotMatrix1522 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1522 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1522 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1522 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1522 (0 : Fin 4) = raw1259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1522 raw1259; decide +kernel
    rw [heq]
    exact (canonical1259 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1522 (1 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1522 (1 : Fin 4) = raw1313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1522 raw1313; decide +kernel
    rw [heq]
    exact (canonical1313 hH).trans (sound831 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1522 (2 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1522 (2 : Fin 4) = raw1320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1522 raw1320; decide +kernel
    rw [heq]
    exact (canonical1320 hH).trans (sound1027 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1522 (3 : Fin 4)) =
      Sparse.eval value841 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1522 (3 : Fin 4) = raw1321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1522 raw1321; decide +kernel
    rw [heq]
    exact (canonical1321 hH).trans (sound841 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1522 + (injectiveMoment H (mergeFirst pivotMatrix1522 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1522 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1522 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1522 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1522, value1027, value804, value831, value841, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1523 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1523 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound1523 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1523 = Sparse.eval value1523 (momentVector H) := by
  have heq : pivotMatrix1523 = (fun u v => node1523 (pivotPermutation1523 u) v) := by apply Matrix.ext; unfold pivotMatrix1523 node1523 pivotPermutation1523; decide +kernel
  have hmoment : injectiveMoment H node1523 = injectiveMoment H pivotMatrix1523 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1523 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1523 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1523 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1523 (0 : Fin 4) = raw2598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1523 raw2598; decide +kernel
    rw [heq]
    exact (canonical2598 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1523 (1 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1523 (1 : Fin 4) = raw1326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1523 raw1326; decide +kernel
    rw [heq]
    exact (canonical1326 hH).trans (sound1027 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1523 (2 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1523 (2 : Fin 4) = raw1307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1523 raw1307; decide +kernel
    rw [heq]
    exact (canonical1307 hH).trans (sound828 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1523 (3 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1523 (3 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1523 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1523 + (injectiveMoment H (mergeFirst pivotMatrix1523 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1523 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1523 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1523 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1523, value1027, value1040, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1524 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1524 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound1524 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1524 = Sparse.eval value1524 (momentVector H) := by
  have heq : pivotMatrix1524 = (fun u v => node1524 (pivotPermutation1524 u) v) := by apply Matrix.ext; unfold pivotMatrix1524 node1524 pivotPermutation1524; decide +kernel
  have hmoment : injectiveMoment H node1524 = injectiveMoment H pivotMatrix1524 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1524 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1524 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1524 (0 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1524 (0 : Fin 4) = raw2438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1524 raw2438; decide +kernel
    rw [heq]
    exact (canonical2438 hH).trans (sound1039 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1524 (1 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1524 (1 : Fin 4) = raw1326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1524 raw1326; decide +kernel
    rw [heq]
    exact (canonical1326 hH).trans (sound1027 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1524 (2 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1524 (2 : Fin 4) = raw1316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1524 raw1316; decide +kernel
    rw [heq]
    exact (canonical1316 hH).trans (sound1237 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1524 (3 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1524 (3 : Fin 4) = raw1315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1524 raw1315; decide +kernel
    rw [heq]
    exact (canonical1315 hH).trans (sound1237 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1524 + (injectiveMoment H (mergeFirst pivotMatrix1524 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1524 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1524 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1524 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1524, value1027, value1039, value1237, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1525 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1525 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound1525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1525 = Sparse.eval value1525 (momentVector H) := by
  have heq : pivotMatrix1525 = (fun u v => node1525 (pivotPermutation1525 u) v) := by apply Matrix.ext; unfold pivotMatrix1525 node1525 pivotPermutation1525; decide +kernel
  have hmoment : injectiveMoment H node1525 = injectiveMoment H pivotMatrix1525 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1525 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1525 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1525 (0 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1525 (0 : Fin 4) = raw2462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1525 raw2462; decide +kernel
    rw [heq]
    exact (canonical2462 hH).trans (sound1044 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1525 (1 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1525 (1 : Fin 4) = raw1327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1525 raw1327; decide +kernel
    rw [heq]
    exact (canonical1327 hH).trans (sound1033 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1525 (2 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1525 (2 : Fin 4) = raw1324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1525 raw1324; decide +kernel
    rw [heq]
    exact (canonical1324 hH).trans (sound1033 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1525 (3 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1525 (3 : Fin 4) = raw1322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1525 raw1322; decide +kernel
    rw [heq]
    exact (canonical1322 hH).trans (sound1237 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1525 + (injectiveMoment H (mergeFirst pivotMatrix1525 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1525 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1525 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1525 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1525, value1033, value1044, value1237, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1526 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem sound1526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1526 = Sparse.eval value1526 (momentVector H) := by
  have heq : pivotMatrix1526 = (fun u v => node1526 (pivotPermutation1526 u) v) := by apply Matrix.ext; unfold pivotMatrix1526 node1526 pivotPermutation1526; decide +kernel
  have hmoment : injectiveMoment H node1526 = injectiveMoment H pivotMatrix1526 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1526 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1526 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1526 (0 : Fin 5)) =
      Sparse.eval value299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1526 (0 : Fin 5) = raw222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1526 raw222; decide +kernel
    rw [heq]
    exact (canonical222 hH).trans (sound299 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1526 (1 : Fin 5)) =
      Sparse.eval value420 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1526 (1 : Fin 5) = raw1338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1526 raw1338; decide +kernel
    rw [heq]
    exact (canonical1338 hH).trans (sound420 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1526 (2 : Fin 5)) =
      Sparse.eval value421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1526 (2 : Fin 5) = raw1390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1526 raw1390; decide +kernel
    rw [heq]
    exact (canonical1390 hH).trans (sound421 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1526 (3 : Fin 5)) =
      Sparse.eval value430 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1526 (3 : Fin 5) = raw1404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1526 raw1404; decide +kernel
    rw [heq]
    exact (canonical1404 hH).trans (sound430 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1526 (4 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1526 (4 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1526 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1526 + (injectiveMoment H (mergeFirst pivotMatrix1526 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1526 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1526 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1526 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1526 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1526, value299, value420, value421, value430, value443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1527 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem sound1527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1527 = Sparse.eval value1527 (momentVector H) := by
  have heq : pivotMatrix1527 = (fun u v => node1527 (pivotPermutation1527 u) v) := by apply Matrix.ext; unfold pivotMatrix1527 node1527 pivotPermutation1527; decide +kernel
  have hmoment : injectiveMoment H node1527 = injectiveMoment H pivotMatrix1527 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1527 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1527 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1527 (0 : Fin 5)) =
      Sparse.eval value300 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1527 (0 : Fin 5) = raw223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1527 raw223; decide +kernel
    rw [heq]
    exact (canonical223 hH).trans (sound300 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1527 (1 : Fin 5)) =
      Sparse.eval value421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1527 (1 : Fin 5) = raw1339 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1527 raw1339; decide +kernel
    rw [heq]
    exact (canonical1339 hH).trans (sound421 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1527 (2 : Fin 5)) =
      Sparse.eval value422 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1527 (2 : Fin 5) = raw1391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1527 raw1391; decide +kernel
    rw [heq]
    exact (canonical1391 hH).trans (sound422 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1527 (3 : Fin 5)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1527 (3 : Fin 5) = raw1405 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1527 raw1405; decide +kernel
    rw [heq]
    exact (canonical1405 hH).trans (sound146 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1527 (4 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1527 (4 : Fin 5) = raw1408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1527 raw1408; decide +kernel
    rw [heq]
    exact (canonical1408 hH).trans (sound443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1527 + (injectiveMoment H (mergeFirst pivotMatrix1527 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1527 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1527 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1527 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1527 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1527, value146, value300, value421, value422, value443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1528 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem sound1528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1528 = Sparse.eval value1528 (momentVector H) := by
  have heq : pivotMatrix1528 = (fun u v => node1528 (pivotPermutation1528 u) v) := by apply Matrix.ext; unfold pivotMatrix1528 node1528 pivotPermutation1528; decide +kernel
  have hmoment : injectiveMoment H node1528 = injectiveMoment H pivotMatrix1528 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1528 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1528 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1528 (0 : Fin 5)) =
      Sparse.eval value303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1528 (0 : Fin 5) = raw234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1528 raw234; decide +kernel
    rw [heq]
    exact (canonical234 hH).trans (sound303 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1528 (1 : Fin 5)) =
      Sparse.eval value419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1528 (1 : Fin 5) = raw1348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1528 raw1348; decide +kernel
    rw [heq]
    exact (canonical1348 hH).trans (sound419 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1528 (2 : Fin 5)) =
      Sparse.eval value434 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1528 (2 : Fin 5) = raw1421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1528 raw1421; decide +kernel
    rw [heq]
    exact (canonical1421 hH).trans (sound434 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1528 (3 : Fin 5)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1528 (3 : Fin 5) = raw1430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1528 raw1430; decide +kernel
    rw [heq]
    exact (canonical1430 hH).trans (sound153 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1528 (4 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1528 (4 : Fin 5) = raw1431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1528 raw1431; decide +kernel
    rw [heq]
    exact (canonical1431 hH).trans (sound443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1528 + (injectiveMoment H (mergeFirst pivotMatrix1528 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1528 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1528 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1528 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1528 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1528, value153, value303, value419, value434, value443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1529 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem sound1529 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1529 = Sparse.eval value1529 (momentVector H) := by
  have heq : pivotMatrix1529 = (fun u v => node1529 (pivotPermutation1529 u) v) := by apply Matrix.ext; unfold pivotMatrix1529 node1529 pivotPermutation1529; decide +kernel
  have hmoment : injectiveMoment H node1529 = injectiveMoment H pivotMatrix1529 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1529 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1529 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1529 (0 : Fin 5)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1529 (0 : Fin 5) = raw282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1529 raw282; decide +kernel
    rw [heq]
    exact (canonical282 hH).trans (sound739 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1529 (1 : Fin 5)) =
      Sparse.eval value421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1529 (1 : Fin 5) = raw1342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1529 raw1342; decide +kernel
    rw [heq]
    exact (canonical1342 hH).trans (sound421 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1529 (2 : Fin 5)) =
      Sparse.eval value421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1529 (2 : Fin 5) = raw1390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1529 raw1390; decide +kernel
    rw [heq]
    exact (canonical1390 hH).trans (sound421 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1529 (3 : Fin 5)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1529 (3 : Fin 5) = raw1397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1529 raw1397; decide +kernel
    rw [heq]
    exact (canonical1397 hH).trans (sound145 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1529 (4 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1529 (4 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1529 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1529 + (injectiveMoment H (mergeFirst pivotMatrix1529 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1529 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1529 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1529 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1529 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1529, value145, value421, value440, value739, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1530 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem sound1530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1530 = Sparse.eval value1530 (momentVector H) := by
  have heq : pivotMatrix1530 = (fun u v => node1530 (pivotPermutation1530 u) v) := by apply Matrix.ext; unfold pivotMatrix1530 node1530 pivotPermutation1530; decide +kernel
  have hmoment : injectiveMoment H node1530 = injectiveMoment H pivotMatrix1530 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1530 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1530 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1530 (0 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1530 (0 : Fin 5) = raw283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1530 raw283; decide +kernel
    rw [heq]
    exact (canonical283 hH).trans (sound742 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1530 (1 : Fin 5)) =
      Sparse.eval value422 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1530 (1 : Fin 5) = raw1343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1530 raw1343; decide +kernel
    rw [heq]
    exact (canonical1343 hH).trans (sound422 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1530 (2 : Fin 5)) =
      Sparse.eval value422 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1530 (2 : Fin 5) = raw1391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1530 raw1391; decide +kernel
    rw [heq]
    exact (canonical1391 hH).trans (sound422 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1530 (3 : Fin 5)) =
      Sparse.eval value437 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1530 (3 : Fin 5) = raw1398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1530 raw1398; decide +kernel
    rw [heq]
    exact (canonical1398 hH).trans (sound437 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1530 (4 : Fin 5)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1530 (4 : Fin 5) = raw1402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1530 raw1402; decide +kernel
    rw [heq]
    exact (canonical1402 hH).trans (sound441 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1530 + (injectiveMoment H (mergeFirst pivotMatrix1530 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1530 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1530 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1530 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1530 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1530, value422, value437, value441, value742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1531 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem sound1531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1531 = Sparse.eval value1531 (momentVector H) := by
  have heq : pivotMatrix1531 = (fun u v => node1531 (pivotPermutation1531 u) v) := by apply Matrix.ext; unfold pivotMatrix1531 node1531 pivotPermutation1531; decide +kernel
  have hmoment : injectiveMoment H node1531 = injectiveMoment H pivotMatrix1531 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1531 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1531 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1531 (0 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1531 (0 : Fin 5) = raw294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1531 raw294; decide +kernel
    rw [heq]
    exact (canonical294 hH).trans (sound737 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1531 (1 : Fin 5)) =
      Sparse.eval value419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1531 (1 : Fin 5) = raw1348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1531 raw1348; decide +kernel
    rw [heq]
    exact (canonical1348 hH).trans (sound419 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1531 (2 : Fin 5)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1531 (2 : Fin 5) = raw1395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1531 raw1395; decide +kernel
    rw [heq]
    exact (canonical1395 hH).trans (sound150 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1531 (3 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1531 (3 : Fin 5) = raw1414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1531 raw1414; decide +kernel
    rw [heq]
    exact (canonical1414 hH).trans (sound440 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1531 (4 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1531 (4 : Fin 5) = raw1415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1531 raw1415; decide +kernel
    rw [heq]
    exact (canonical1415 hH).trans (sound443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1531 + (injectiveMoment H (mergeFirst pivotMatrix1531 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1531 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1531 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1531 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1531 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1531, value150, value419, value440, value443, value737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1532 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem sound1532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1532 = Sparse.eval value1532 (momentVector H) := by
  have heq : pivotMatrix1532 = (fun u v => node1532 (pivotPermutation1532 u) v) := by apply Matrix.ext; unfold pivotMatrix1532 node1532 pivotPermutation1532; decide +kernel
  have hmoment : injectiveMoment H node1532 = injectiveMoment H pivotMatrix1532 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1532 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1532 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1532 (0 : Fin 5)) =
      Sparse.eval value376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1532 (0 : Fin 5) = raw2681 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1532 raw2681; decide +kernel
    rw [heq]
    exact (canonical2681 hH).trans (sound376 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1532 (1 : Fin 5)) =
      Sparse.eval value426 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1532 (1 : Fin 5) = raw1356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1532 raw1356; decide +kernel
    rw [heq]
    exact (canonical1356 hH).trans (sound426 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1532 (2 : Fin 5)) =
      Sparse.eval value423 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1532 (2 : Fin 5) = raw1344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1532 raw1344; decide +kernel
    rw [heq]
    exact (canonical1344 hH).trans (sound423 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1532 (3 : Fin 5)) =
      Sparse.eval value422 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1532 (3 : Fin 5) = raw1343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1532 raw1343; decide +kernel
    rw [heq]
    exact (canonical1343 hH).trans (sound422 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1532 (4 : Fin 5)) =
      Sparse.eval value421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1532 (4 : Fin 5) = raw1342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1532 raw1342; decide +kernel
    rw [heq]
    exact (canonical1342 hH).trans (sound421 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1532 + (injectiveMoment H (mergeFirst pivotMatrix1532 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1532 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1532 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1532 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1532 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1532, value376, value421, value422, value423, value426, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1533 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem sound1533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1533 = Sparse.eval value1533 (momentVector H) := by
  have heq : pivotMatrix1533 = (fun u v => node1533 (pivotPermutation1533 u) v) := by apply Matrix.ext; unfold pivotMatrix1533 node1533 pivotPermutation1533; decide +kernel
  have hmoment : injectiveMoment H node1533 = injectiveMoment H pivotMatrix1533 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1533 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1533 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1533 (0 : Fin 5)) =
      Sparse.eval value374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1533 (0 : Fin 5) = raw2689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1533 raw2689; decide +kernel
    rw [heq]
    exact (canonical2689 hH).trans (sound374 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1533 (1 : Fin 5)) =
      Sparse.eval value427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1533 (1 : Fin 5) = raw1357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1533 raw1357; decide +kernel
    rw [heq]
    exact (canonical1357 hH).trans (sound427 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1533 (2 : Fin 5)) =
      Sparse.eval value419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1533 (2 : Fin 5) = raw1350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1533 raw1350; decide +kernel
    rw [heq]
    exact (canonical1350 hH).trans (sound419 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1533 (3 : Fin 5)) =
      Sparse.eval value419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1533 (3 : Fin 5) = raw1348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1533 raw1348; decide +kernel
    rw [heq]
    exact (canonical1348 hH).trans (sound419 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1533 (4 : Fin 5)) =
      Sparse.eval value425 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1533 (4 : Fin 5) = raw1347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1533 raw1347; decide +kernel
    rw [heq]
    exact (canonical1347 hH).trans (sound425 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1533 + (injectiveMoment H (mergeFirst pivotMatrix1533 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1533 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1533 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1533 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1533 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1533, value374, value419, value425, value427, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1534 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound1534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1534 = Sparse.eval value1534 (momentVector H) := by
  have heq : pivotMatrix1534 = (fun u v => node1534 (pivotPermutation1534 u) v) := by apply Matrix.ext; unfold pivotMatrix1534 node1534 pivotPermutation1534; decide +kernel
  have hmoment : injectiveMoment H node1534 = injectiveMoment H pivotMatrix1534 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1534 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1534 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1534 (0 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1534 (0 : Fin 5) = raw5496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1534 raw5496; decide +kernel
    rw [heq]
    exact (canonical5496 hH).trans (sound743 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1534 (1 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1534 (1 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1534 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1534 (2 : Fin 5)) =
      Sparse.eval value419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1534 (2 : Fin 5) = raw1352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1534 raw1352; decide +kernel
    rw [heq]
    exact (canonical1352 hH).trans (sound419 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1534 (3 : Fin 5)) =
      Sparse.eval value424 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1534 (3 : Fin 5) = raw1345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1534 raw1345; decide +kernel
    rw [heq]
    exact (canonical1345 hH).trans (sound424 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1534 (4 : Fin 5)) =
      Sparse.eval value423 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1534 (4 : Fin 5) = raw1344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1534 raw1344; decide +kernel
    rw [heq]
    exact (canonical1344 hH).trans (sound423 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1534 + (injectiveMoment H (mergeFirst pivotMatrix1534 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1534 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1534 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1534 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1534 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1534, value419, value423, value424, value443, value743, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1535 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1535 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem sound1535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1535 = Sparse.eval value1535 (momentVector H) := by
  have heq : pivotMatrix1535 = (fun u v => node1535 (pivotPermutation1535 u) v) := by apply Matrix.ext; unfold pivotMatrix1535 node1535 pivotPermutation1535; decide +kernel
  have hmoment : injectiveMoment H node1535 = injectiveMoment H pivotMatrix1535 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1535 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1535 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1535 (0 : Fin 5)) =
      Sparse.eval value372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1535 (0 : Fin 5) = raw2700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1535 raw2700; decide +kernel
    rw [heq]
    exact (canonical2700 hH).trans (sound372 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1535 (1 : Fin 5)) =
      Sparse.eval value428 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1535 (1 : Fin 5) = raw1363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1535 raw1363; decide +kernel
    rw [heq]
    exact (canonical1363 hH).trans (sound428 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1535 (2 : Fin 5)) =
      Sparse.eval value362 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1535 (2 : Fin 5) = raw1360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1535 raw1360; decide +kernel
    rw [heq]
    exact (canonical1360 hH).trans (sound362 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1535 (3 : Fin 5)) =
      Sparse.eval value362 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1535 (3 : Fin 5) = raw1358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1535 raw1358; decide +kernel
    rw [heq]
    exact (canonical1358 hH).trans (sound362 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1535 (4 : Fin 5)) =
      Sparse.eval value427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1535 (4 : Fin 5) = raw1357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1535 raw1357; decide +kernel
    rw [heq]
    exact (canonical1357 hH).trans (sound427 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1535 + (injectiveMoment H (mergeFirst pivotMatrix1535 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1535 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1535 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1535 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1535 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1535, value362, value372, value427, value428, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
