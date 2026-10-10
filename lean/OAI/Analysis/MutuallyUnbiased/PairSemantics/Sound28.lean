import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values28
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical71
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical119
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical121
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1792 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1792 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem sound1792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1792 = Sparse.eval value1792 (momentVector H) := by
  have heq : pivotMatrix1792 = (fun u v => node1792 (pivotPermutation1792 u) v) := by apply Matrix.ext; unfold pivotMatrix1792 node1792 pivotPermutation1792; decide +kernel
  have hmoment : injectiveMoment H node1792 = injectiveMoment H pivotMatrix1792 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1792 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1792 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1792 (0 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1792 (0 : Fin 4) = raw2618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1792 raw2618; decide +kernel
    rw [heq]
    exact (canonical2618 hH).trans (sound1096 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1792 (1 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1792 (1 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1792 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1792 (2 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1792 (2 : Fin 4) = raw2458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1792 raw2458; decide +kernel
    rw [heq]
    exact (canonical2458 hH).trans (sound1260 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1792 (3 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1792 (3 : Fin 4) = raw2457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1792 raw2457; decide +kernel
    rw [heq]
    exact (canonical2457 hH).trans (sound835 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1792 + (injectiveMoment H (mergeFirst pivotMatrix1792 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1792 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1792 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1792 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1792, value1096, value1260, value514, value835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1793 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1793 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound1793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1793 = Sparse.eval value1793 (momentVector H) := by
  have heq : pivotMatrix1793 = (fun u v => node1793 (pivotPermutation1793 u) v) := by apply Matrix.ext; unfold pivotMatrix1793 node1793 pivotPermutation1793; decide +kernel
  have hmoment : injectiveMoment H node1793 = injectiveMoment H pivotMatrix1793 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1793 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1793 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1793 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1793 (0 : Fin 4) = raw2619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1793 raw2619; decide +kernel
    rw [heq]
    exact (canonical2619 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1793 (1 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1793 (1 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1793 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1793 (2 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1793 (2 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1793 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1793 (3 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1793 (3 : Fin 4) = raw2458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1793 raw2458; decide +kernel
    rw [heq]
    exact (canonical2458 hH).trans (sound1260 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1793 + (injectiveMoment H (mergeFirst pivotMatrix1793 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1793 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1793 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1793 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1793, value1058, value1078, value1260, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1794 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1794 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem sound1794 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1794 = Sparse.eval value1794 (momentVector H) := by
  have heq : pivotMatrix1794 = (fun u v => node1794 (pivotPermutation1794 u) v) := by apply Matrix.ext; unfold pivotMatrix1794 node1794 pivotPermutation1794; decide +kernel
  have hmoment : injectiveMoment H node1794 = injectiveMoment H pivotMatrix1794 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1794 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1794 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1794 (0 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1794 (0 : Fin 4) = raw2620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1794 raw2620; decide +kernel
    rw [heq]
    exact (canonical2620 hH).trans (sound1123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1794 (1 : Fin 4)) =
      Sparse.eval value515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1794 (1 : Fin 4) = raw2472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1794 raw2472; decide +kernel
    rw [heq]
    exact (canonical2472 hH).trans (sound515 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1794 (2 : Fin 4)) =
      Sparse.eval value851 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1794 (2 : Fin 4) = raw2460 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1794 raw2460; decide +kernel
    rw [heq]
    exact (canonical2460 hH).trans (sound851 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1794 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1794 (3 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1794 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1794 + (injectiveMoment H (mergeFirst pivotMatrix1794 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1794 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1794 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1794 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1794, value1078, value1123, value515, value851, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1795 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1795 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

theorem sound1795 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1795 = Sparse.eval value1795 (momentVector H) := by
  have heq : pivotMatrix1795 = (fun u v => node1795 (pivotPermutation1795 u) v) := by apply Matrix.ext; unfold pivotMatrix1795 node1795 pivotPermutation1795; decide +kernel
  have hmoment : injectiveMoment H node1795 = injectiveMoment H pivotMatrix1795 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1795 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1795 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1795 (0 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1795 (0 : Fin 4) = raw2621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1795 raw2621; decide +kernel
    rw [heq]
    exact (canonical2621 hH).trans (sound513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1795 (1 : Fin 4)) =
      Sparse.eval value516 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1795 (1 : Fin 4) = raw2477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1795 raw2477; decide +kernel
    rw [heq]
    exact (canonical2477 hH).trans (sound516 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1795 (2 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1795 (2 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1795 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1795 (3 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1795 (3 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1795 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1795 + (injectiveMoment H (mergeFirst pivotMatrix1795 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1795 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1795 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1795 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1795, value1058, value513, value514, value516, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1796 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1796 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem sound1796 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1796 = Sparse.eval value1796 (momentVector H) := by
  have heq : pivotMatrix1796 = (fun u v => node1796 (pivotPermutation1796 u) v) := by apply Matrix.ext; unfold pivotMatrix1796 node1796 pivotPermutation1796; decide +kernel
  have hmoment : injectiveMoment H node1796 = injectiveMoment H pivotMatrix1796 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1796 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1796 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1796 (0 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1796 (0 : Fin 4) = raw2622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1796 raw2622; decide +kernel
    rw [heq]
    exact (canonical2622 hH).trans (sound1249 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1796 (1 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1796 (1 : Fin 4) = raw2478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1796 raw2478; decide +kernel
    rw [heq]
    exact (canonical2478 hH).trans (sound1018 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1796 (2 : Fin 4)) =
      Sparse.eval value515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1796 (2 : Fin 4) = raw2472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1796 raw2472; decide +kernel
    rw [heq]
    exact (canonical2472 hH).trans (sound515 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1796 (3 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1796 (3 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1796 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1796 + (injectiveMoment H (mergeFirst pivotMatrix1796 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1796 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1796 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1796 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1796, value1018, value1058, value1249, value515, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1797 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1797 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound1797 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1797 = Sparse.eval value1797 (momentVector H) := by
  have heq : pivotMatrix1797 = (fun u v => node1797 (pivotPermutation1797 u) v) := by apply Matrix.ext; unfold pivotMatrix1797 node1797 pivotPermutation1797; decide +kernel
  have hmoment : injectiveMoment H node1797 = injectiveMoment H pivotMatrix1797 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1797 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1797 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1797 (0 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1797 (0 : Fin 4) = raw2623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1797 raw2623; decide +kernel
    rw [heq]
    exact (canonical2623 hH).trans (sound1016 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1797 (1 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1797 (1 : Fin 4) = raw2485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1797 raw2485; decide +kernel
    rw [heq]
    exact (canonical2485 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1797 (2 : Fin 4)) =
      Sparse.eval value505 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1797 (2 : Fin 4) = raw2482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1797 raw2482; decide +kernel
    rw [heq]
    exact (canonical2482 hH).trans (sound505 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1797 (3 : Fin 4)) =
      Sparse.eval value990 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1797 (3 : Fin 4) = raw2481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1797 raw2481; decide +kernel
    rw [heq]
    exact (canonical2481 hH).trans (sound990 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1797 + (injectiveMoment H (mergeFirst pivotMatrix1797 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1797 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1797 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1797 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1797, value1010, value1016, value505, value990, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1798 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1798 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound1798 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1798 = Sparse.eval value1798 (momentVector H) := by
  have heq : pivotMatrix1798 = (fun u v => node1798 (pivotPermutation1798 u) v) := by apply Matrix.ext; unfold pivotMatrix1798 node1798 pivotPermutation1798; decide +kernel
  have hmoment : injectiveMoment H node1798 = injectiveMoment H pivotMatrix1798 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1798 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1798 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1798 (0 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1798 (0 : Fin 4) = raw2624 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1798 raw2624; decide +kernel
    rw [heq]
    exact (canonical2624 hH).trans (sound1013 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1798 (1 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1798 (1 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1798 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1798 (2 : Fin 4)) =
      Sparse.eval value823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1798 (2 : Fin 4) = raw2483 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1798 raw2483; decide +kernel
    rw [heq]
    exact (canonical2483 hH).trans (sound823 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1798 (3 : Fin 4)) =
      Sparse.eval value505 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1798 (3 : Fin 4) = raw2482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1798 raw2482; decide +kernel
    rw [heq]
    exact (canonical2482 hH).trans (sound505 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1798 + (injectiveMoment H (mergeFirst pivotMatrix1798 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1798 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1798 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1798 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1798, value1005, value1013, value505, value823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1799 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1799 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem sound1799 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1799 = Sparse.eval value1799 (momentVector H) := by
  have heq : pivotMatrix1799 = (fun u v => node1799 (pivotPermutation1799 u) v) := by apply Matrix.ext; unfold pivotMatrix1799 node1799 pivotPermutation1799; decide +kernel
  have hmoment : injectiveMoment H node1799 = injectiveMoment H pivotMatrix1799 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1799 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1799 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1799 (0 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1799 (0 : Fin 4) = raw2626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1799 raw2626; decide +kernel
    rw [heq]
    exact (canonical2626 hH).trans (sound510 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1799 (1 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1799 (1 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1799 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1799 (2 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1799 (2 : Fin 4) = raw2485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1799 raw2485; decide +kernel
    rw [heq]
    exact (canonical2485 hH).trans (sound1010 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1799 (3 : Fin 4)) =
      Sparse.eval value511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1799 (3 : Fin 4) = raw2484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1799 raw2484; decide +kernel
    rw [heq]
    exact (canonical2484 hH).trans (sound511 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1799 + (injectiveMoment H (mergeFirst pivotMatrix1799 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1799 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1799 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1799 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1799, value1010, value510, value511, value517, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1800 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1800 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound1800 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1800 = Sparse.eval value1800 (momentVector H) := by
  have heq : pivotMatrix1800 = (fun u v => node1800 (pivotPermutation1800 u) v) := by apply Matrix.ext; unfold pivotMatrix1800 node1800 pivotPermutation1800; decide +kernel
  have hmoment : injectiveMoment H node1800 = injectiveMoment H pivotMatrix1800 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1800 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1800 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1800 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1800 (0 : Fin 4) = raw2627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1800 raw2627; decide +kernel
    rw [heq]
    exact (canonical2627 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1800 (1 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1800 (1 : Fin 4) = raw2490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1800 raw2490; decide +kernel
    rw [heq]
    exact (canonical2490 hH).trans (sound1047 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1800 (2 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1800 (2 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1800 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1800 (3 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1800 (3 : Fin 4) = raw2485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1800 raw2485; decide +kernel
    rw [heq]
    exact (canonical2485 hH).trans (sound1010 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1800 + (injectiveMoment H (mergeFirst pivotMatrix1800 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1800 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1800 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1800 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1800, value1005, value1010, value1047, value1053, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1801 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1801 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound1801 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1801 = Sparse.eval value1801 (momentVector H) := by
  have heq : pivotMatrix1801 = (fun u v => node1801 (pivotPermutation1801 u) v) := by apply Matrix.ext; unfold pivotMatrix1801 node1801 pivotPermutation1801; decide +kernel
  have hmoment : injectiveMoment H node1801 = injectiveMoment H pivotMatrix1801 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1801 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1801 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1801 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1801 (0 : Fin 4) = raw2628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1801 raw2628; decide +kernel
    rw [heq]
    exact (canonical2628 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1801 (1 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1801 (1 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1801 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1801 (2 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1801 (2 : Fin 4) = raw2490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1801 raw2490; decide +kernel
    rw [heq]
    exact (canonical2490 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1801 (3 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1801 (3 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1801 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1801 + (injectiveMoment H (mergeFirst pivotMatrix1801 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1801 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1801 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1801 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1801, value1047, value1078, value517, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1802 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1802 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

theorem sound1802 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1802 = Sparse.eval value1802 (momentVector H) := by
  have heq : pivotMatrix1802 = (fun u v => node1802 (pivotPermutation1802 u) v) := by apply Matrix.ext; unfold pivotMatrix1802 node1802 pivotPermutation1802; decide +kernel
  have hmoment : injectiveMoment H node1802 = injectiveMoment H pivotMatrix1802 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1802 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1802 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1802 (0 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1802 (0 : Fin 4) = raw2629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1802 raw2629; decide +kernel
    rw [heq]
    exact (canonical2629 hH).trans (sound844 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1802 (1 : Fin 4)) =
      Sparse.eval value731 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1802 (1 : Fin 4) = raw2498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1802 raw2498; decide +kernel
    rw [heq]
    exact (canonical2498 hH).trans (sound731 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1802 (2 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1802 (2 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1802 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1802 (3 : Fin 4)) =
      Sparse.eval value518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1802 (3 : Fin 4) = raw2493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1802 raw2493; decide +kernel
    rw [heq]
    exact (canonical2493 hH).trans (sound518 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1802 + (injectiveMoment H (mergeFirst pivotMatrix1802 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1802 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1802 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1802 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1802, value518, value731, value837, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1803 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1803 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound1803 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1803 = Sparse.eval value1803 (momentVector H) := by
  have heq : pivotMatrix1803 = (fun u v => node1803 (pivotPermutation1803 u) v) := by apply Matrix.ext; unfold pivotMatrix1803 node1803 pivotPermutation1803; decide +kernel
  have hmoment : injectiveMoment H node1803 = injectiveMoment H pivotMatrix1803 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1803 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1803 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1803 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1803 (0 : Fin 4) = raw2630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1803 raw2630; decide +kernel
    rw [heq]
    exact (canonical2630 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1803 (1 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1803 (1 : Fin 4) = raw2499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1803 raw2499; decide +kernel
    rw [heq]
    exact (canonical2499 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1803 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1803 (2 : Fin 4) = raw2495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1803 raw2495; decide +kernel
    rw [heq]
    exact (canonical2495 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1803 (3 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1803 (3 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1803 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1803 + (injectiveMoment H (mergeFirst pivotMatrix1803 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1803 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1803 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1803 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1803, value1005, value1013, value1053, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1804 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1804 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound1804 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1804 = Sparse.eval value1804 (momentVector H) := by
  have heq : pivotMatrix1804 = (fun u v => node1804 (pivotPermutation1804 u) v) := by apply Matrix.ext; unfold pivotMatrix1804 node1804 pivotPermutation1804; decide +kernel
  have hmoment : injectiveMoment H node1804 = injectiveMoment H pivotMatrix1804 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1804 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1804 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1804 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1804 (0 : Fin 4) = raw2631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1804 raw2631; decide +kernel
    rw [heq]
    exact (canonical2631 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1804 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1804 (1 : Fin 4) = raw2500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1804 raw2500; decide +kernel
    rw [heq]
    exact (canonical2500 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1804 (2 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1804 (2 : Fin 4) = raw2496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1804 raw2496; decide +kernel
    rw [heq]
    exact (canonical2496 hH).trans (sound510 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1804 (3 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1804 (3 : Fin 4) = raw2495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1804 raw2495; decide +kernel
    rw [heq]
    exact (canonical2495 hH).trans (sound1053 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1804 + (injectiveMoment H (mergeFirst pivotMatrix1804 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1804 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1804 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1804 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1804, value1010, value1016, value1053, value510, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1805 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1805 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

theorem sound1805 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1805 = Sparse.eval value1805 (momentVector H) := by
  have heq : pivotMatrix1805 = (fun u v => node1805 (pivotPermutation1805 u) v) := by apply Matrix.ext; unfold pivotMatrix1805 node1805 pivotPermutation1805; decide +kernel
  have hmoment : injectiveMoment H node1805 = injectiveMoment H pivotMatrix1805 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1805 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1805 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1805 (0 : Fin 4)) =
      Sparse.eval value823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1805 (0 : Fin 4) = raw2633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1805 raw2633; decide +kernel
    rw [heq]
    exact (canonical2633 hH).trans (sound823 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1805 (1 : Fin 4)) =
      Sparse.eval value821 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1805 (1 : Fin 4) = raw2502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1805 raw2502; decide +kernel
    rw [heq]
    exact (canonical2502 hH).trans (sound821 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1805 (2 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1805 (2 : Fin 4) = raw2499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1805 raw2499; decide +kernel
    rw [heq]
    exact (canonical2499 hH).trans (sound1013 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1805 (3 : Fin 4)) =
      Sparse.eval value731 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1805 (3 : Fin 4) = raw2498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1805 raw2498; decide +kernel
    rw [heq]
    exact (canonical2498 hH).trans (sound731 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1805 + (injectiveMoment H (mergeFirst pivotMatrix1805 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1805 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1805 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1805 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1805, value1013, value731, value821, value823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1806 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1806 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

theorem sound1806 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1806 = Sparse.eval value1806 (momentVector H) := by
  have heq : pivotMatrix1806 = (fun u v => node1806 (pivotPermutation1806 u) v) := by apply Matrix.ext; unfold pivotMatrix1806 node1806 pivotPermutation1806; decide +kernel
  have hmoment : injectiveMoment H node1806 = injectiveMoment H pivotMatrix1806 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1806 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1806 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1806 (0 : Fin 4)) =
      Sparse.eval value505 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1806 (0 : Fin 4) = raw2634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1806 raw2634; decide +kernel
    rw [heq]
    exact (canonical2634 hH).trans (sound505 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1806 (1 : Fin 4)) =
      Sparse.eval value501 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1806 (1 : Fin 4) = raw2503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1806 raw2503; decide +kernel
    rw [heq]
    exact (canonical2503 hH).trans (sound501 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1806 (2 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1806 (2 : Fin 4) = raw2500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1806 raw2500; decide +kernel
    rw [heq]
    exact (canonical2500 hH).trans (sound1016 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1806 (3 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1806 (3 : Fin 4) = raw2499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1806 raw2499; decide +kernel
    rw [heq]
    exact (canonical2499 hH).trans (sound1013 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1806 + (injectiveMoment H (mergeFirst pivotMatrix1806 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1806 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1806 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1806 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1806, value1013, value1016, value501, value505, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1807 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1807 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

theorem sound1807 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1807 = Sparse.eval value1807 (momentVector H) := by
  have heq : pivotMatrix1807 = (fun u v => node1807 (pivotPermutation1807 u) v) := by apply Matrix.ext; unfold pivotMatrix1807 node1807 pivotPermutation1807; decide +kernel
  have hmoment : injectiveMoment H node1807 = injectiveMoment H pivotMatrix1807 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1807 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1807 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1807 (0 : Fin 4)) =
      Sparse.eval value990 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1807 (0 : Fin 4) = raw2635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1807 raw2635; decide +kernel
    rw [heq]
    exact (canonical2635 hH).trans (sound990 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1807 (1 : Fin 4)) =
      Sparse.eval value1076 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1807 (1 : Fin 4) = raw2504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1807 raw2504; decide +kernel
    rw [heq]
    exact (canonical2504 hH).trans (sound1076 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1807 (2 : Fin 4)) =
      Sparse.eval value519 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1807 (2 : Fin 4) = raw2501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1807 raw2501; decide +kernel
    rw [heq]
    exact (canonical2501 hH).trans (sound519 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1807 (3 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1807 (3 : Fin 4) = raw2500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1807 raw2500; decide +kernel
    rw [heq]
    exact (canonical2500 hH).trans (sound1016 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1807 + (injectiveMoment H (mergeFirst pivotMatrix1807 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1807 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1807 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1807 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1807, value1016, value1076, value519, value990, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1808 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1808 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

theorem sound1808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1808 = Sparse.eval value1808 (momentVector H) := by
  have heq : pivotMatrix1808 = (fun u v => node1808 (pivotPermutation1808 u) v) := by apply Matrix.ext; unfold pivotMatrix1808 node1808 pivotPermutation1808; decide +kernel
  have hmoment : injectiveMoment H node1808 = injectiveMoment H pivotMatrix1808 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1808 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1808 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1808 (0 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1808 (0 : Fin 4) = raw3498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1808 raw3498; decide +kernel
    rw [heq]
    exact (canonical3498 hH).trans (sound1314 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1808 (1 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1808 (1 : Fin 4) = raw2465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1808 raw2465; decide +kernel
    rw [heq]
    exact (canonical2465 hH).trans (sound510 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1808 (2 : Fin 4)) =
      Sparse.eval value504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1808 (2 : Fin 4) = raw2375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1808 raw2375; decide +kernel
    rw [heq]
    exact (canonical2375 hH).trans (sound504 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1808 (3 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1808 (3 : Fin 4) = raw2363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1808 raw2363; decide +kernel
    rw [heq]
    exact (canonical2363 hH).trans (sound844 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1808 + (injectiveMoment H (mergeFirst pivotMatrix1808 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1808 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1808 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1808 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1808, value1314, value504, value510, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1809 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1809 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

theorem sound1809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1809 = Sparse.eval value1809 (momentVector H) := by
  have heq : pivotMatrix1809 = (fun u v => node1809 (pivotPermutation1809 u) v) := by apply Matrix.ext; unfold pivotMatrix1809 node1809 pivotPermutation1809; decide +kernel
  have hmoment : injectiveMoment H node1809 = injectiveMoment H pivotMatrix1809 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1809 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1809 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1809 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1809 (0 : Fin 4) = raw3780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1809 raw3780; decide +kernel
    rw [heq]
    exact (canonical3780 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1809 (1 : Fin 4)) =
      Sparse.eval value511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1809 (1 : Fin 4) = raw2476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1809 raw2476; decide +kernel
    rw [heq]
    exact (canonical2476 hH).trans (sound511 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1809 (2 : Fin 4)) =
      Sparse.eval value523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1809 (2 : Fin 4) = raw2378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1809 raw2378; decide +kernel
    rw [heq]
    exact (canonical2378 hH).trans (sound523 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1809 (3 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1809 (3 : Fin 4) = raw2363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1809 raw2363; decide +kernel
    rw [heq]
    exact (canonical2363 hH).trans (sound844 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1809 + (injectiveMoment H (mergeFirst pivotMatrix1809 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1809 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1809 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1809 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1809, value1010, value511, value523, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1810 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1810 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem sound1810 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1810 = Sparse.eval value1810 (momentVector H) := by
  have heq : pivotMatrix1810 = (fun u v => node1810 (pivotPermutation1810 u) v) := by apply Matrix.ext; unfold pivotMatrix1810 node1810 pivotPermutation1810; decide +kernel
  have hmoment : injectiveMoment H node1810 = injectiveMoment H pivotMatrix1810 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1810 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1810 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1810 (0 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1810 (0 : Fin 4) = raw3503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1810 raw3503; decide +kernel
    rw [heq]
    exact (canonical3503 hH).trans (sound854 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1810 (1 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1810 (1 : Fin 4) = raw2469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1810 raw2469; decide +kernel
    rw [heq]
    exact (canonical2469 hH).trans (sound842 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1810 (2 : Fin 4)) =
      Sparse.eval value507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1810 (2 : Fin 4) = raw2380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1810 raw2380; decide +kernel
    rw [heq]
    exact (canonical2380 hH).trans (sound507 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1810 (3 : Fin 4)) =
      Sparse.eval value843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1810 (3 : Fin 4) = raw2373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1810 raw2373; decide +kernel
    rw [heq]
    exact (canonical2373 hH).trans (sound843 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1810 + (injectiveMoment H (mergeFirst pivotMatrix1810 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1810 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1810 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1810 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1810, value507, value842, value843, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1811 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1811 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem sound1811 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1811 = Sparse.eval value1811 (momentVector H) := by
  have heq : pivotMatrix1811 = (fun u v => node1811 (pivotPermutation1811 u) v) := by apply Matrix.ext; unfold pivotMatrix1811 node1811 pivotPermutation1811; decide +kernel
  have hmoment : injectiveMoment H node1811 = injectiveMoment H pivotMatrix1811 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1811 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1811 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1811 (0 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1811 (0 : Fin 4) = raw3506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1811 raw3506; decide +kernel
    rw [heq]
    exact (canonical3506 hH).trans (sound1112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1811 (1 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1811 (1 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1811 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1811 (2 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1811 (2 : Fin 4) = raw2383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1811 raw2383; decide +kernel
    rw [heq]
    exact (canonical2383 hH).trans (sound842 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1811 (3 : Fin 4)) =
      Sparse.eval value508 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1811 (3 : Fin 4) = raw2381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1811 raw2381; decide +kernel
    rw [heq]
    exact (canonical2381 hH).trans (sound508 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1811 + (injectiveMoment H (mergeFirst pivotMatrix1811 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1811 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1811 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1811 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1811, value1112, value508, value514, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1812 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1812 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

theorem sound1812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1812 = Sparse.eval value1812 (momentVector H) := by
  have heq : pivotMatrix1812 = (fun u v => node1812 (pivotPermutation1812 u) v) := by apply Matrix.ext; unfold pivotMatrix1812 node1812 pivotPermutation1812; decide +kernel
  have hmoment : injectiveMoment H node1812 = injectiveMoment H pivotMatrix1812 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1812 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1812 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1812 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1812 (0 : Fin 4) = raw3784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1812 raw3784; decide +kernel
    rw [heq]
    exact (canonical3784 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1812 (1 : Fin 4)) =
      Sparse.eval value516 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1812 (1 : Fin 4) = raw2477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1812 raw2477; decide +kernel
    rw [heq]
    exact (canonical2477 hH).trans (sound516 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1812 (2 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1812 (2 : Fin 4) = raw2384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1812 raw2384; decide +kernel
    rw [heq]
    exact (canonical2384 hH).trans (sound853 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1812 (3 : Fin 4)) =
      Sparse.eval value508 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1812 (3 : Fin 4) = raw2381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1812 raw2381; decide +kernel
    rw [heq]
    exact (canonical2381 hH).trans (sound508 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1812 + (injectiveMoment H (mergeFirst pivotMatrix1812 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1812 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1812 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1812 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1812, value1058, value508, value516, value853, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1813 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1813 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem sound1813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1813 = Sparse.eval value1813 (momentVector H) := by
  have heq : pivotMatrix1813 = (fun u v => node1813 (pivotPermutation1813 u) v) := by apply Matrix.ext; unfold pivotMatrix1813 node1813 pivotPermutation1813; decide +kernel
  have hmoment : injectiveMoment H node1813 = injectiveMoment H pivotMatrix1813 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1813 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1813 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1813 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1813 (0 : Fin 4) = raw3785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1813 raw3785; decide +kernel
    rw [heq]
    exact (canonical3785 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1813 (1 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1813 (1 : Fin 4) = raw2478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1813 raw2478; decide +kernel
    rw [heq]
    exact (canonical2478 hH).trans (sound1018 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1813 (2 : Fin 4)) =
      Sparse.eval value839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1813 (2 : Fin 4) = raw2385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1813 raw2385; decide +kernel
    rw [heq]
    exact (canonical2385 hH).trans (sound839 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1813 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1813 (3 : Fin 4) = raw2382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1813 raw2382; decide +kernel
    rw [heq]
    exact (canonical2382 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1813 + (injectiveMoment H (mergeFirst pivotMatrix1813 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1813 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1813 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1813 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1813, value1018, value1235, value839, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1814 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1814 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem sound1814 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1814 = Sparse.eval value1814 (momentVector H) := by
  have heq : pivotMatrix1814 = (fun u v => node1814 (pivotPermutation1814 u) v) := by apply Matrix.ext; unfold pivotMatrix1814 node1814 pivotPermutation1814; decide +kernel
  have hmoment : injectiveMoment H node1814 = injectiveMoment H pivotMatrix1814 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1814 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1814 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1814 (0 : Fin 4)) =
      Sparse.eval value843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1814 (0 : Fin 4) = raw5772 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1814 raw5772; decide +kernel
    rw [heq]
    exact (canonical5772 hH).trans (sound843 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1814 (1 : Fin 4)) =
      Sparse.eval value823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1814 (1 : Fin 4) = raw2514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1814 raw2514; decide +kernel
    rw [heq]
    exact (canonical2514 hH).trans (sound823 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1814 (2 : Fin 4)) =
      Sparse.eval value839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1814 (2 : Fin 4) = raw2386 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1814 raw2386; decide +kernel
    rw [heq]
    exact (canonical2386 hH).trans (sound839 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1814 (3 : Fin 4)) =
      Sparse.eval value504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1814 (3 : Fin 4) = raw2375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1814 raw2375; decide +kernel
    rw [heq]
    exact (canonical2375 hH).trans (sound504 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1814 + (injectiveMoment H (mergeFirst pivotMatrix1814 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1814 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1814 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1814 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1814, value504, value823, value839, value843, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1815 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1815 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem sound1815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1815 = Sparse.eval value1815 (momentVector H) := by
  have heq : pivotMatrix1815 = (fun u v => node1815 (pivotPermutation1815 u) v) := by apply Matrix.ext; unfold pivotMatrix1815 node1815 pivotPermutation1815; decide +kernel
  have hmoment : injectiveMoment H node1815 = injectiveMoment H pivotMatrix1815 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1815 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1815 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1815 (0 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1815 (0 : Fin 4) = raw6683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1815 raw6683; decide +kernel
    rw [heq]
    exact (canonical6683 hH).trans (sound1112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1815 (1 : Fin 4)) =
      Sparse.eval value511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1815 (1 : Fin 4) = raw2520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1815 raw2520; decide +kernel
    rw [heq]
    exact (canonical2520 hH).trans (sound511 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1815 (2 : Fin 4)) =
      Sparse.eval value508 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1815 (2 : Fin 4) = raw2387 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1815 raw2387; decide +kernel
    rw [heq]
    exact (canonical2387 hH).trans (sound508 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1815 (3 : Fin 4)) =
      Sparse.eval value523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1815 (3 : Fin 4) = raw2378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1815 raw2378; decide +kernel
    rw [heq]
    exact (canonical2378 hH).trans (sound523 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1815 + (injectiveMoment H (mergeFirst pivotMatrix1815 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1815 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1815 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1815 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1815, value1112, value508, value511, value523, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1816 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1816 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem sound1816 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1816 = Sparse.eval value1816 (momentVector H) := by
  have heq : pivotMatrix1816 = (fun u v => node1816 (pivotPermutation1816 u) v) := by apply Matrix.ext; unfold pivotMatrix1816 node1816 pivotPermutation1816; decide +kernel
  have hmoment : injectiveMoment H node1816 = injectiveMoment H pivotMatrix1816 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1816 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1816 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1816 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1816 (0 : Fin 4) = raw6508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1816 raw6508; decide +kernel
    rw [heq]
    exact (canonical6508 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1816 (1 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1816 (1 : Fin 4) = raw2519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1816 raw2519; decide +kernel
    rw [heq]
    exact (canonical2519 hH).trans (sound517 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1816 (2 : Fin 4)) =
      Sparse.eval value508 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1816 (2 : Fin 4) = raw2387 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1816 raw2387; decide +kernel
    rw [heq]
    exact (canonical2387 hH).trans (sound508 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1816 (3 : Fin 4)) =
      Sparse.eval value507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1816 (3 : Fin 4) = raw2380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1816 raw2380; decide +kernel
    rw [heq]
    exact (canonical2380 hH).trans (sound507 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1816 + (injectiveMoment H (mergeFirst pivotMatrix1816 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1816 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1816 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1816 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1816, value1058, value507, value508, value517, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1817 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1817 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound1817 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1817 = Sparse.eval value1817 (momentVector H) := by
  have heq : pivotMatrix1817 = (fun u v => node1817 (pivotPermutation1817 u) v) := by apply Matrix.ext; unfold pivotMatrix1817 node1817 pivotPermutation1817; decide +kernel
  have hmoment : injectiveMoment H node1817 = injectiveMoment H pivotMatrix1817 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1817 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1817 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1817 (0 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1817 (0 : Fin 4) = raw3543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1817 raw3543; decide +kernel
    rw [heq]
    exact (canonical3543 hH).trans (sound1301 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1817 (1 : Fin 4)) =
      Sparse.eval value990 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1817 (1 : Fin 4) = raw2481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1817 raw2481; decide +kernel
    rw [heq]
    exact (canonical2481 hH).trans (sound990 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1817 (2 : Fin 4)) =
      Sparse.eval value850 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1817 (2 : Fin 4) = raw2405 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1817 raw2405; decide +kernel
    rw [heq]
    exact (canonical2405 hH).trans (sound850 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1817 (3 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1817 (3 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1817 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1817 + (injectiveMoment H (mergeFirst pivotMatrix1817 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1817 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1817 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1817 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1817, value1249, value1301, value850, value990, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1818 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1818 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound1818 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1818 = Sparse.eval value1818 (momentVector H) := by
  have heq : pivotMatrix1818 = (fun u v => node1818 (pivotPermutation1818 u) v) := by apply Matrix.ext; unfold pivotMatrix1818 node1818 pivotPermutation1818; decide +kernel
  have hmoment : injectiveMoment H node1818 = injectiveMoment H pivotMatrix1818 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1818 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1818 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1818 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1818 (0 : Fin 4) = raw3806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1818 raw3806; decide +kernel
    rw [heq]
    exact (canonical3806 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1818 (1 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1818 (1 : Fin 4) = raw2485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1818 raw2485; decide +kernel
    rw [heq]
    exact (canonical2485 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1818 (2 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1818 (2 : Fin 4) = raw2406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1818 raw2406; decide +kernel
    rw [heq]
    exact (canonical2406 hH).trans (sound838 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1818 (3 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1818 (3 : Fin 4) = raw2403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1818 raw2403; decide +kernel
    rw [heq]
    exact (canonical2403 hH).trans (sound1249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1818 + (injectiveMoment H (mergeFirst pivotMatrix1818 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1818 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1818 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1818 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1818, value1009, value1010, value1249, value838, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1819 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1819 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound1819 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1819 = Sparse.eval value1819 (momentVector H) := by
  have heq : pivotMatrix1819 = (fun u v => node1819 (pivotPermutation1819 u) v) := by apply Matrix.ext; unfold pivotMatrix1819 node1819 pivotPermutation1819; decide +kernel
  have hmoment : injectiveMoment H node1819 = injectiveMoment H pivotMatrix1819 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1819 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1819 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1819 (0 : Fin 4)) =
      Sparse.eval value1006 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1819 (0 : Fin 4) = raw3807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1819 raw3807; decide +kernel
    rw [heq]
    exact (canonical3807 hH).trans (sound1006 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1819 (1 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1819 (1 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1819 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1819 (2 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1819 (2 : Fin 4) = raw2407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1819 raw2407; decide +kernel
    rw [heq]
    exact (canonical2407 hH).trans (sound838 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1819 (3 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1819 (3 : Fin 4) = raw2404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1819 raw2404; decide +kernel
    rw [heq]
    exact (canonical2404 hH).trans (sound513 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1819 + (injectiveMoment H (mergeFirst pivotMatrix1819 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1819 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1819 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1819 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1819, value1005, value1006, value513, value838, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1820 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1820 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound1820 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1820 = Sparse.eval value1820 (momentVector H) := by
  have heq : pivotMatrix1820 = (fun u v => node1820 (pivotPermutation1820 u) v) := by apply Matrix.ext; unfold pivotMatrix1820 node1820 pivotPermutation1820; decide +kernel
  have hmoment : injectiveMoment H node1820 = injectiveMoment H pivotMatrix1820 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1820 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1820 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1820 (0 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1820 (0 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1820 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1820 (1 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1820 (1 : Fin 4) = raw2516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1820 raw2516; decide +kernel
    rw [heq]
    exact (canonical2516 hH).trans (sound845 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1820 (2 : Fin 4)) =
      Sparse.eval value838 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1820 (2 : Fin 4) = raw2407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1820 raw2407; decide +kernel
    rw [heq]
    exact (canonical2407 hH).trans (sound838 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1820 (3 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1820 (3 : Fin 4) = raw2399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1820 raw2399; decide +kernel
    rw [heq]
    exact (canonical2399 hH).trans (sound510 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1820 + (injectiveMoment H (mergeFirst pivotMatrix1820 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1820 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1820 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1820 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1820, value510, value838, value845, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1821 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1821 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound1821 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1821 = Sparse.eval value1821 (momentVector H) := by
  have heq : pivotMatrix1821 = (fun u v => node1821 (pivotPermutation1821 u) v) := by apply Matrix.ext; unfold pivotMatrix1821 node1821 pivotPermutation1821; decide +kernel
  have hmoment : injectiveMoment H node1821 = injectiveMoment H pivotMatrix1821 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1821 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1821 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1821 (0 : Fin 4)) =
      Sparse.eval value847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1821 (0 : Fin 4) = raw5779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1821 raw5779; decide +kernel
    rw [heq]
    exact (canonical5779 hH).trans (sound847 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1821 (1 : Fin 4)) =
      Sparse.eval value836 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1821 (1 : Fin 4) = raw2517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1821 raw2517; decide +kernel
    rw [heq]
    exact (canonical2517 hH).trans (sound836 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1821 (2 : Fin 4)) =
      Sparse.eval value850 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1821 (2 : Fin 4) = raw2408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1821 raw2408; decide +kernel
    rw [heq]
    exact (canonical2408 hH).trans (sound850 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1821 (3 : Fin 4)) =
      Sparse.eval value511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1821 (3 : Fin 4) = raw2401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1821 raw2401; decide +kernel
    rw [heq]
    exact (canonical2401 hH).trans (sound511 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1821 + (injectiveMoment H (mergeFirst pivotMatrix1821 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1821 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1821 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1821 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1821, value511, value836, value847, value850, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1822 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1822 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem sound1822 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1822 = Sparse.eval value1822 (momentVector H) := by
  have heq : pivotMatrix1822 = (fun u v => node1822 (pivotPermutation1822 u) v) := by apply Matrix.ext; unfold pivotMatrix1822 node1822 pivotPermutation1822; decide +kernel
  have hmoment : injectiveMoment H node1822 = injectiveMoment H pivotMatrix1822 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1822 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1822 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1822 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1822 (0 : Fin 4) = raw3587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1822 raw3587; decide +kernel
    rw [heq]
    exact (canonical3587 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1822 (1 : Fin 4)) =
      Sparse.eval value511 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1822 (1 : Fin 4) = raw2484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1822 raw2484; decide +kernel
    rw [heq]
    exact (canonical2484 hH).trans (sound511 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1822 (2 : Fin 4)) =
      Sparse.eval value847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1822 (2 : Fin 4) = raw2436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1822 raw2436; decide +kernel
    rw [heq]
    exact (canonical2436 hH).trans (sound847 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1822 (3 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1822 (3 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1822 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1822 + (injectiveMoment H (mergeFirst pivotMatrix1822 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1822 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1822 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1822 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1822, value1079, value1123, value511, value847, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1823 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1823 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound1823 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1823 = Sparse.eval value1823 (momentVector H) := by
  have heq : pivotMatrix1823 = (fun u v => node1823 (pivotPermutation1823 u) v) := by apply Matrix.ext; unfold pivotMatrix1823 node1823 pivotPermutation1823; decide +kernel
  have hmoment : injectiveMoment H node1823 = injectiveMoment H pivotMatrix1823 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1823 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1823 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1823 (0 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1823 (0 : Fin 4) = raw3588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1823 raw3588; decide +kernel
    rw [heq]
    exact (canonical3588 hH).trans (sound1241 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1823 (1 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1823 (1 : Fin 4) = raw2486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1823 raw2486; decide +kernel
    rw [heq]
    exact (canonical2486 hH).trans (sound1005 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1823 (2 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1823 (2 : Fin 4) = raw2438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1823 raw2438; decide +kernel
    rw [heq]
    exact (canonical2438 hH).trans (sound1039 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1823 (3 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1823 (3 : Fin 4) = raw2435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1823 raw2435; decide +kernel
    rw [heq]
    exact (canonical2435 hH).trans (sound1096 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1823 + (injectiveMoment H (mergeFirst pivotMatrix1823 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1823 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1823 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1823 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1823, value1005, value1039, value1096, value1241, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1824 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1824 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem sound1824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1824 = Sparse.eval value1824 (momentVector H) := by
  have heq : pivotMatrix1824 = (fun u v => node1824 (pivotPermutation1824 u) v) := by apply Matrix.ext; unfold pivotMatrix1824 node1824 pivotPermutation1824; decide +kernel
  have hmoment : injectiveMoment H node1824 = injectiveMoment H pivotMatrix1824 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1824 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1824 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1824 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1824 (0 : Fin 4) = raw3593 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1824 raw3593; decide +kernel
    rw [heq]
    exact (canonical3593 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1824 (1 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1824 (1 : Fin 4) = raw2489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1824 raw2489; decide +kernel
    rw [heq]
    exact (canonical2489 hH).trans (sound517 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1824 (2 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1824 (2 : Fin 4) = raw2461 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1824 raw2461; decide +kernel
    rw [heq]
    exact (canonical2461 hH).trans (sound846 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1824 (3 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1824 (3 : Fin 4) = raw2457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1824 raw2457; decide +kernel
    rw [heq]
    exact (canonical2457 hH).trans (sound835 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1824 + (injectiveMoment H (mergeFirst pivotMatrix1824 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1824 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1824 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1824 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1824, value1110, value517, value835, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1825 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound1825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1825 = Sparse.eval value1825 (momentVector H) := by
  have heq : pivotMatrix1825 = (fun u v => node1825 (pivotPermutation1825 u) v) := by apply Matrix.ext; unfold pivotMatrix1825 node1825 pivotPermutation1825; decide +kernel
  have hmoment : injectiveMoment H node1825 = injectiveMoment H pivotMatrix1825 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1825 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1825 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1825 (0 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1825 (0 : Fin 4) = raw3594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1825 raw3594; decide +kernel
    rw [heq]
    exact (canonical3594 hH).trans (sound1242 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1825 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1825 (1 : Fin 4) = raw2491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1825 raw2491; decide +kernel
    rw [heq]
    exact (canonical2491 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1825 (2 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1825 (2 : Fin 4) = raw2463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1825 raw2463; decide +kernel
    rw [heq]
    exact (canonical2463 hH).trans (sound1044 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1825 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1825 (3 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1825 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1825 + (injectiveMoment H (mergeFirst pivotMatrix1825 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1825 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1825 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1825 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1825, value1044, value1078, value1242, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1826 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1826 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound1826 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1826 = Sparse.eval value1826 (momentVector H) := by
  have heq : pivotMatrix1826 = (fun u v => node1826 (pivotPermutation1826 u) v) := by apply Matrix.ext; unfold pivotMatrix1826 node1826 pivotPermutation1826; decide +kernel
  have hmoment : injectiveMoment H node1826 = injectiveMoment H pivotMatrix1826 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1826 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1826 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1826 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1826 (0 : Fin 4) = raw3598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1826 raw3598; decide +kernel
    rw [heq]
    exact (canonical3598 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1826 (1 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1826 (1 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1826 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1826 (2 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1826 (2 : Fin 4) = raw2473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1826 raw2473; decide +kernel
    rw [heq]
    exact (canonical2473 hH).trans (sound845 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1826 (3 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1826 (3 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1826 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1826 + (injectiveMoment H (mergeFirst pivotMatrix1826 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1826 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1826 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1826 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1826, value1040, value514, value837, value845, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1827 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1827 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound1827 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1827 = Sparse.eval value1827 (momentVector H) := by
  have heq : pivotMatrix1827 = (fun u v => node1827 (pivotPermutation1827 u) v) := by apply Matrix.ext; unfold pivotMatrix1827 node1827 pivotPermutation1827; decide +kernel
  have hmoment : injectiveMoment H node1827 = injectiveMoment H pivotMatrix1827 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1827 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1827 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1827 (0 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1827 (0 : Fin 4) = raw3601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1827 raw3601; decide +kernel
    rw [heq]
    exact (canonical3601 hH).trans (sound805 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1827 (1 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1827 (1 : Fin 4) = raw2499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1827 raw2499; decide +kernel
    rw [heq]
    exact (canonical2499 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1827 (2 : Fin 4)) =
      Sparse.eval value836 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1827 (2 : Fin 4) = raw2479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1827 raw2479; decide +kernel
    rw [heq]
    exact (canonical2479 hH).trans (sound836 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1827 (3 : Fin 4)) =
      Sparse.eval value516 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1827 (3 : Fin 4) = raw2477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1827 raw2477; decide +kernel
    rw [heq]
    exact (canonical2477 hH).trans (sound516 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1827 + (injectiveMoment H (mergeFirst pivotMatrix1827 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1827 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1827 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1827 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1827, value1013, value516, value805, value836, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1828 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1828 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound1828 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1828 = Sparse.eval value1828 (momentVector H) := by
  have heq : pivotMatrix1828 = (fun u v => node1828 (pivotPermutation1828 u) v) := by apply Matrix.ext; unfold pivotMatrix1828 node1828 pivotPermutation1828; decide +kernel
  have hmoment : injectiveMoment H node1828 = injectiveMoment H pivotMatrix1828 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1828 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1828 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1828 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1828 (0 : Fin 4) = raw3602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1828 raw3602; decide +kernel
    rw [heq]
    exact (canonical3602 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1828 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1828 (1 : Fin 4) = raw2500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1828 raw2500; decide +kernel
    rw [heq]
    exact (canonical2500 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1828 (2 : Fin 4)) =
      Sparse.eval value836 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1828 (2 : Fin 4) = raw2480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1828 raw2480; decide +kernel
    rw [heq]
    exact (canonical2480 hH).trans (sound836 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1828 (3 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1828 (3 : Fin 4) = raw2478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1828 raw2478; decide +kernel
    rw [heq]
    exact (canonical2478 hH).trans (sound1018 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1828 + (injectiveMoment H (mergeFirst pivotMatrix1828 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1828 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1828 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1828 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1828, value1016, value1018, value807, value836, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1829 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1829 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem sound1829 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1829 = Sparse.eval value1829 (momentVector H) := by
  have heq : pivotMatrix1829 = (fun u v => node1829 (pivotPermutation1829 u) v) := by apply Matrix.ext; unfold pivotMatrix1829 node1829 pivotPermutation1829; decide +kernel
  have hmoment : injectiveMoment H node1829 = injectiveMoment H pivotMatrix1829 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1829 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1829 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1829 (0 : Fin 4)) =
      Sparse.eval value1126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1829 (0 : Fin 4) = raw3834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1829 raw3834; decide +kernel
    rw [heq]
    exact (canonical3834 hH).trans (sound1126 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1829 (1 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1829 (1 : Fin 4) = raw2496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1829 raw2496; decide +kernel
    rw [heq]
    exact (canonical2496 hH).trans (sound510 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1829 (2 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1829 (2 : Fin 4) = raw2464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1829 raw2464; decide +kernel
    rw [heq]
    exact (canonical2464 hH).trans (sound846 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1829 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1829 (3 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1829 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1829 + (injectiveMoment H (mergeFirst pivotMatrix1829 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1829 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1829 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1829 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1829, value1078, value1126, value510, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1830 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1830 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound1830 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1830 = Sparse.eval value1830 (momentVector H) := by
  have heq : pivotMatrix1830 = (fun u v => node1830 (pivotPermutation1830 u) v) := by apply Matrix.ext; unfold pivotMatrix1830 node1830 pivotPermutation1830; decide +kernel
  have hmoment : injectiveMoment H node1830 = injectiveMoment H pivotMatrix1830 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1830 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1830 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1830 (0 : Fin 4)) =
      Sparse.eval value1006 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1830 (0 : Fin 4) = raw3838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1830 raw3838; decide +kernel
    rw [heq]
    exact (canonical3838 hH).trans (sound1006 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1830 (1 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1830 (1 : Fin 4) = raw2499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1830 raw2499; decide +kernel
    rw [heq]
    exact (canonical2499 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1830 (2 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1830 (2 : Fin 4) = raw2474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1830 raw2474; decide +kernel
    rw [heq]
    exact (canonical2474 hH).trans (sound1040 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1830 (3 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1830 (3 : Fin 4) = raw2470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1830 raw2470; decide +kernel
    rw [heq]
    exact (canonical2470 hH).trans (sound514 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1830 + (injectiveMoment H (mergeFirst pivotMatrix1830 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1830 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1830 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1830 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1830, value1006, value1013, value1040, value514, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1831 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1831 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound1831 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1831 = Sparse.eval value1831 (momentVector H) := by
  have heq : pivotMatrix1831 = (fun u v => node1831 (pivotPermutation1831 u) v) := by apply Matrix.ext; unfold pivotMatrix1831 node1831 pivotPermutation1831; decide +kernel
  have hmoment : injectiveMoment H node1831 = injectiveMoment H pivotMatrix1831 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1831 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1831 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1831 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1831 (0 : Fin 4) = raw3839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1831 raw3839; decide +kernel
    rw [heq]
    exact (canonical3839 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1831 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1831 (1 : Fin 4) = raw2500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1831 raw2500; decide +kernel
    rw [heq]
    exact (canonical2500 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1831 (2 : Fin 4)) =
      Sparse.eval value845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1831 (2 : Fin 4) = raw2475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1831 raw2475; decide +kernel
    rw [heq]
    exact (canonical2475 hH).trans (sound845 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1831 (3 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1831 (3 : Fin 4) = raw2471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1831 raw2471; decide +kernel
    rw [heq]
    exact (canonical2471 hH).trans (sound1058 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1831 + (injectiveMoment H (mergeFirst pivotMatrix1831 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1831 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1831 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1831 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1831, value1009, value1016, value1058, value845, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1832 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem sound1832 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1832 = Sparse.eval value1832 (momentVector H) := by
  have heq : pivotMatrix1832 = (fun u v => node1832 (pivotPermutation1832 u) v) := by apply Matrix.ext; unfold pivotMatrix1832 node1832 pivotPermutation1832; decide +kernel
  have hmoment : injectiveMoment H node1832 = injectiveMoment H pivotMatrix1832 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1832 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1832 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1832 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1832 (0 : Fin 4) = raw2168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1832 raw2168; decide +kernel
    rw [heq]
    exact (canonical2168 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1832 (1 : Fin 4)) =
      Sparse.eval value482 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1832 (1 : Fin 4) = raw2533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1832 raw2533; decide +kernel
    rw [heq]
    exact (canonical2533 hH).trans (sound482 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1832 (2 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1832 (2 : Fin 4) = raw2542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1832 raw2542; decide +kernel
    rw [heq]
    exact (canonical2542 hH).trans (sound520 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1832 (3 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1832 (3 : Fin 4) = raw2544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1832 raw2544; decide +kernel
    rw [heq]
    exact (canonical2544 hH).trans (sound521 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1832 + (injectiveMoment H (mergeFirst pivotMatrix1832 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1832 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1832 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1832 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1832, value1059, value482, value520, value521, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1833 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1833 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem sound1833 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1833 = Sparse.eval value1833 (momentVector H) := by
  have heq : pivotMatrix1833 = (fun u v => node1833 (pivotPermutation1833 u) v) := by apply Matrix.ext; unfold pivotMatrix1833 node1833 pivotPermutation1833; decide +kernel
  have hmoment : injectiveMoment H node1833 = injectiveMoment H pivotMatrix1833 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1833 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1833 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1833 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1833 (0 : Fin 4) = raw3688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1833 raw3688; decide +kernel
    rw [heq]
    exact (canonical3688 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1833 (1 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1833 (1 : Fin 4) = raw2555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1833 raw2555; decide +kernel
    rw [heq]
    exact (canonical2555 hH).trans (sound854 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1833 (2 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1833 (2 : Fin 4) = raw2542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1833 raw2542; decide +kernel
    rw [heq]
    exact (canonical2542 hH).trans (sound520 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1833 (3 : Fin 4)) =
      Sparse.eval value1346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1833 (3 : Fin 4) = raw2540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1833 raw2540; decide +kernel
    rw [heq]
    exact (canonical2540 hH).trans (sound1346 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1833 + (injectiveMoment H (mergeFirst pivotMatrix1833 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1833 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1833 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1833 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1833, value1053, value1346, value520, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1834 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1834 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1834 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1834 = Sparse.eval value1834 (momentVector H) := by
  have heq : pivotMatrix1834 = (fun u v => node1834 (pivotPermutation1834 u) v) := by apply Matrix.ext; unfold pivotMatrix1834 node1834 pivotPermutation1834; decide +kernel
  have hmoment : injectiveMoment H node1834 = injectiveMoment H pivotMatrix1834 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1834 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1834 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1834 (0 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1834 (0 : Fin 4) = raw3695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1834 raw3695; decide +kernel
    rw [heq]
    exact (canonical3695 hH).trans (sound1047 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1834 (1 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1834 (1 : Fin 4) = raw2561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1834 raw2561; decide +kernel
    rw [heq]
    exact (canonical2561 hH).trans (sound853 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1834 (2 : Fin 4)) =
      Sparse.eval value522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1834 (2 : Fin 4) = raw2547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1834 raw2547; decide +kernel
    rw [heq]
    exact (canonical2547 hH).trans (sound522 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1834 (3 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1834 (3 : Fin 4) = raw2546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1834 raw2546; decide +kernel
    rw [heq]
    exact (canonical2546 hH).trans (sound1276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1834 + (injectiveMoment H (mergeFirst pivotMatrix1834 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1834 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1834 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1834 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1834, value1047, value1276, value522, value853, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1835 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1835 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1835 = Sparse.eval value1835 (momentVector H) := by
  have heq : pivotMatrix1835 = (fun u v => node1835 (pivotPermutation1835 u) v) := by apply Matrix.ext; unfold pivotMatrix1835 node1835 pivotPermutation1835; decide +kernel
  have hmoment : injectiveMoment H node1835 = injectiveMoment H pivotMatrix1835 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1835 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1835 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1835 (0 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1835 (0 : Fin 4) = raw4186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1835 raw4186; decide +kernel
    rw [heq]
    exact (canonical4186 hH).trans (sound1008 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1835 (1 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1835 (1 : Fin 4) = raw2578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1835 raw2578; decide +kernel
    rw [heq]
    exact (canonical2578 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1835 (2 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1835 (2 : Fin 4) = raw2544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1835 raw2544; decide +kernel
    rw [heq]
    exact (canonical2544 hH).trans (sound521 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1835 (3 : Fin 4)) =
      Sparse.eval value1346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1835 (3 : Fin 4) = raw2540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1835 raw2540; decide +kernel
    rw [heq]
    exact (canonical2540 hH).trans (sound1346 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1835 + (injectiveMoment H (mergeFirst pivotMatrix1835 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1835 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1835 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1835 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1835, value1008, value1265, value1346, value521, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1836 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1836 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound1836 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1836 = Sparse.eval value1836 (momentVector H) := by
  have heq : pivotMatrix1836 = (fun u v => node1836 (pivotPermutation1836 u) v) := by apply Matrix.ext; unfold pivotMatrix1836 node1836 pivotPermutation1836; decide +kernel
  have hmoment : injectiveMoment H node1836 = injectiveMoment H pivotMatrix1836 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1836 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1836 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1836 (0 : Fin 4)) =
      Sparse.eval value1002 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1836 (0 : Fin 4) = raw4187 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1836 raw4187; decide +kernel
    rw [heq]
    exact (canonical4187 hH).trans (sound1002 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1836 (1 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1836 (1 : Fin 4) = raw2586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1836 raw2586; decide +kernel
    rw [heq]
    exact (canonical2586 hH).trans (sound1047 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1836 (2 : Fin 4)) =
      Sparse.eval value522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1836 (2 : Fin 4) = raw2547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1836 raw2547; decide +kernel
    rw [heq]
    exact (canonical2547 hH).trans (sound522 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1836 (3 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1836 (3 : Fin 4) = raw2545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1836 raw2545; decide +kernel
    rw [heq]
    exact (canonical2545 hH).trans (sound1007 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1836 + (injectiveMoment H (mergeFirst pivotMatrix1836 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1836 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1836 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1836 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1836, value1002, value1007, value1047, value522, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1837 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1837 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound1837 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1837 = Sparse.eval value1837 (momentVector H) := by
  have heq : pivotMatrix1837 = (fun u v => node1837 (pivotPermutation1837 u) v) := by apply Matrix.ext; unfold pivotMatrix1837 node1837 pivotPermutation1837; decide +kernel
  have hmoment : injectiveMoment H node1837 = injectiveMoment H pivotMatrix1837 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1837 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1837 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1837 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1837 (0 : Fin 4) = raw6921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1837 raw6921; decide +kernel
    rw [heq]
    exact (canonical6921 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1837 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1837 (1 : Fin 4) = raw2646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1837 raw2646; decide +kernel
    rw [heq]
    exact (canonical2646 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1837 (2 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1837 (2 : Fin 4) = raw2548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1837 raw2548; decide +kernel
    rw [heq]
    exact (canonical2548 hH).trans (sound1276 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1837 (3 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1837 (3 : Fin 4) = raw2542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1837 raw2542; decide +kernel
    rw [heq]
    exact (canonical2542 hH).trans (sound520 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1837 + (injectiveMoment H (mergeFirst pivotMatrix1837 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1837 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1837 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1837 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1837, value1009, value1078, value1276, value520, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1838 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1838 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound1838 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1838 = Sparse.eval value1838 (momentVector H) := by
  have heq : pivotMatrix1838 = (fun u v => node1838 (pivotPermutation1838 u) v) := by apply Matrix.ext; unfold pivotMatrix1838 node1838 pivotPermutation1838; decide +kernel
  have hmoment : injectiveMoment H node1838 = injectiveMoment H pivotMatrix1838 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1838 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1838 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1838 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1838 (0 : Fin 4) = raw6612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1838 raw6612; decide +kernel
    rw [heq]
    exact (canonical6612 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1838 (1 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1838 (1 : Fin 4) = raw2644 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1838 raw2644; decide +kernel
    rw [heq]
    exact (canonical2644 hH).trans (sound844 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1838 (2 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1838 (2 : Fin 4) = raw2548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1838 raw2548; decide +kernel
    rw [heq]
    exact (canonical2548 hH).trans (sound1276 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1838 (3 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1838 (3 : Fin 4) = raw2544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1838 raw2544; decide +kernel
    rw [heq]
    exact (canonical2544 hH).trans (sound521 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1838 + (injectiveMoment H (mergeFirst pivotMatrix1838 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1838 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1838 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1838 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1838, value1265, value1276, value521, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1839 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1839 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem sound1839 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1839 = Sparse.eval value1839 (momentVector H) := by
  have heq : pivotMatrix1839 = (fun u v => node1839 (pivotPermutation1839 u) v) := by apply Matrix.ext; unfold pivotMatrix1839 node1839 pivotPermutation1839; decide +kernel
  have hmoment : injectiveMoment H node1839 = injectiveMoment H pivotMatrix1839 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1839 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1839 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1839 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1839 (0 : Fin 4) = raw1292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1839 raw1292; decide +kernel
    rw [heq]
    exact (canonical1292 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1839 (1 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1839 (1 : Fin 4) = raw2542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1839 raw2542; decide +kernel
    rw [heq]
    exact (canonical2542 hH).trans (sound520 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1839 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1839 (2 : Fin 4) = raw2573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1839 raw2573; decide +kernel
    rw [heq]
    exact (canonical2573 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1839 (3 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1839 (3 : Fin 4) = raw2581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1839 raw2581; decide +kernel
    rw [heq]
    exact (canonical2581 hH).trans (sound1058 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1839 + (injectiveMoment H (mergeFirst pivotMatrix1839 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1839 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1839 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1839 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1839, value1053, value1058, value1059, value520, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1840 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1840 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem sound1840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1840 = Sparse.eval value1840 (momentVector H) := by
  have heq : pivotMatrix1840 = (fun u v => node1840 (pivotPermutation1840 u) v) := by apply Matrix.ext; unfold pivotMatrix1840 node1840 pivotPermutation1840; decide +kernel
  have hmoment : injectiveMoment H node1840 = injectiveMoment H pivotMatrix1840 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1840 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1840 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1840 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (0 : Fin 4) = raw1294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw1294; decide +kernel
    rw [heq]
    exact (canonical1294 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1840 (1 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (1 : Fin 4) = raw2544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw2544; decide +kernel
    rw [heq]
    exact (canonical2544 hH).trans (sound521 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1840 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (2 : Fin 4) = raw2578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw2578; decide +kernel
    rw [heq]
    exact (canonical2578 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1840 (3 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1840 (3 : Fin 4) = raw2585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1840 raw2585; decide +kernel
    rw [heq]
    exact (canonical2585 hH).trans (sound1010 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1840 + (injectiveMoment H (mergeFirst pivotMatrix1840 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1840 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1840 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1840 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1840, value1010, value1059, value1265, value521, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1841 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1841 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem sound1841 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1841 = Sparse.eval value1841 (momentVector H) := by
  have heq : pivotMatrix1841 = (fun u v => node1841 (pivotPermutation1841 u) v) := by apply Matrix.ext; unfold pivotMatrix1841 node1841 pivotPermutation1841; decide +kernel
  have hmoment : injectiveMoment H node1841 = injectiveMoment H pivotMatrix1841 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1841 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1841 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1841 (0 : Fin 4)) =
      Sparse.eval value1084 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (0 : Fin 4) = raw1295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw1295; decide +kernel
    rw [heq]
    exact (canonical1295 hH).trans (sound1084 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1841 (1 : Fin 4)) =
      Sparse.eval value522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (1 : Fin 4) = raw2547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw2547; decide +kernel
    rw [heq]
    exact (canonical2547 hH).trans (sound522 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1841 (2 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (2 : Fin 4) = raw2586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw2586; decide +kernel
    rw [heq]
    exact (canonical2586 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1841 (3 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1841 (3 : Fin 4) = raw2587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1841 raw2587; decide +kernel
    rw [heq]
    exact (canonical2587 hH).trans (sound1260 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1841 + (injectiveMoment H (mergeFirst pivotMatrix1841 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1841 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1841 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1841 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1841, value1047, value1084, value1260, value522, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1842 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1842 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem sound1842 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1842 = Sparse.eval value1842 (momentVector H) := by
  have heq : pivotMatrix1842 = (fun u v => node1842 (pivotPermutation1842 u) v) := by apply Matrix.ext; unfold pivotMatrix1842 node1842 pivotPermutation1842; decide +kernel
  have hmoment : injectiveMoment H node1842 = injectiveMoment H pivotMatrix1842 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1842 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1842 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1842 (0 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1842 (0 : Fin 4) = raw1306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1842 raw1306; decide +kernel
    rw [heq]
    exact (canonical1306 hH).trans (sound828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1842 (1 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1842 (1 : Fin 4) = raw2561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1842 raw2561; decide +kernel
    rw [heq]
    exact (canonical2561 hH).trans (sound853 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1842 (2 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1842 (2 : Fin 4) = raw2597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1842 raw2597; decide +kernel
    rw [heq]
    exact (canonical2597 hH).trans (sound1058 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1842 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1842 (3 : Fin 4) = raw2598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1842 raw2598; decide +kernel
    rw [heq]
    exact (canonical2598 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1842 + (injectiveMoment H (mergeFirst pivotMatrix1842 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1842 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1842 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1842 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1842, value1040, value1058, value828, value853, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1843 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1843 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem sound1843 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1843 = Sparse.eval value1843 (momentVector H) := by
  have heq : pivotMatrix1843 = (fun u v => node1843 (pivotPermutation1843 u) v) := by apply Matrix.ext; unfold pivotMatrix1843 node1843 pivotPermutation1843; decide +kernel
  have hmoment : injectiveMoment H node1843 = injectiveMoment H pivotMatrix1843 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1843 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1843 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1843 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1843 (0 : Fin 4) = raw4190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1843 raw4190; decide +kernel
    rw [heq]
    exact (canonical4190 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1843 (1 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1843 (1 : Fin 4) = raw2594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1843 raw2594; decide +kernel
    rw [heq]
    exact (canonical2594 hH).trans (sound1112 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1843 (2 : Fin 4)) =
      Sparse.eval value523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1843 (2 : Fin 4) = raw2558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1843 raw2558; decide +kernel
    rw [heq]
    exact (canonical2558 hH).trans (sound523 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1843 (3 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1843 (3 : Fin 4) = raw2555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1843 raw2555; decide +kernel
    rw [heq]
    exact (canonical2555 hH).trans (sound854 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1843 + (injectiveMoment H (mergeFirst pivotMatrix1843 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1843 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1843 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1843 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1843, value1057, value1112, value523, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1844 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1844 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound1844 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1844 = Sparse.eval value1844 (momentVector H) := by
  have heq : pivotMatrix1844 = (fun u v => node1844 (pivotPermutation1844 u) v) := by apply Matrix.ext; unfold pivotMatrix1844 node1844 pivotPermutation1844; decide +kernel
  have hmoment : injectiveMoment H node1844 = injectiveMoment H pivotMatrix1844 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1844 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1844 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1844 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1844 (0 : Fin 4) = raw4191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1844 raw4191; decide +kernel
    rw [heq]
    exact (canonical4191 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1844 (1 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1844 (1 : Fin 4) = raw2597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1844 raw2597; decide +kernel
    rw [heq]
    exact (canonical2597 hH).trans (sound1058 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1844 (2 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1844 (2 : Fin 4) = raw2561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1844 raw2561; decide +kernel
    rw [heq]
    exact (canonical2561 hH).trans (sound853 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1844 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1844 (3 : Fin 4) = raw2560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1844 raw2560; decide +kernel
    rw [heq]
    exact (canonical2560 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1844 + (injectiveMoment H (mergeFirst pivotMatrix1844 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1844 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1844 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1844 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1844, value1057, value1058, value1235, value853, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1845 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1845 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound1845 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1845 = Sparse.eval value1845 (momentVector H) := by
  have heq : pivotMatrix1845 = (fun u v => node1845 (pivotPermutation1845 u) v) := by apply Matrix.ext; unfold pivotMatrix1845 node1845 pivotPermutation1845; decide +kernel
  have hmoment : injectiveMoment H node1845 = injectiveMoment H pivotMatrix1845 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1845 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1845 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1845 (0 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1845 (0 : Fin 4) = raw5823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1845 raw5823; decide +kernel
    rw [heq]
    exact (canonical5823 hH).trans (sound854 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1845 (1 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1845 (1 : Fin 4) = raw2644 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1845 raw2644; decide +kernel
    rw [heq]
    exact (canonical2644 hH).trans (sound844 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1845 (2 : Fin 4)) =
      Sparse.eval value853 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1845 (2 : Fin 4) = raw2562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1845 raw2562; decide +kernel
    rw [heq]
    exact (canonical2562 hH).trans (sound853 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1845 (3 : Fin 4)) =
      Sparse.eval value523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1845 (3 : Fin 4) = raw2558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1845 raw2558; decide +kernel
    rw [heq]
    exact (canonical2558 hH).trans (sound523 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1845 + (injectiveMoment H (mergeFirst pivotMatrix1845 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1845 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1845 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1845 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1845, value523, value844, value853, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1846 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1846 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem sound1846 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1846 = Sparse.eval value1846 (momentVector H) := by
  have heq : pivotMatrix1846 = (fun u v => node1846 (pivotPermutation1846 u) v) := by apply Matrix.ext; unfold pivotMatrix1846 node1846 pivotPermutation1846; decide +kernel
  have hmoment : injectiveMoment H node1846 = injectiveMoment H pivotMatrix1846 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1846 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1846 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1846 (0 : Fin 4)) =
      Sparse.eval value1281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1846 (0 : Fin 4) = raw2277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1846 raw2277; decide +kernel
    rw [heq]
    exact (canonical2277 hH).trans (sound1281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1846 (1 : Fin 4)) =
      Sparse.eval value523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1846 (1 : Fin 4) = raw2558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1846 raw2558; decide +kernel
    rw [heq]
    exact (canonical2558 hH).trans (sound523 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1846 (2 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1846 (2 : Fin 4) = raw2581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1846 raw2581; decide +kernel
    rw [heq]
    exact (canonical2581 hH).trans (sound1058 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1846 (3 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1846 (3 : Fin 4) = raw2585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1846 raw2585; decide +kernel
    rw [heq]
    exact (canonical2585 hH).trans (sound1010 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1846 + (injectiveMoment H (mergeFirst pivotMatrix1846 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1846 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1846 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1846 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1846, value1010, value1058, value1281, value523, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1847 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1847 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound1847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1847 = Sparse.eval value1847 (momentVector H) := by
  have heq : pivotMatrix1847 = (fun u v => node1847 (pivotPermutation1847 u) v) := by apply Matrix.ext; unfold pivotMatrix1847 node1847 pivotPermutation1847; decide +kernel
  have hmoment : injectiveMoment H node1847 = injectiveMoment H pivotMatrix1847 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1847 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1847 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1847 (0 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1847 (0 : Fin 4) = raw2457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1847 raw2457; decide +kernel
    rw [heq]
    exact (canonical2457 hH).trans (sound835 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1847 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1847 (1 : Fin 4) = raw2608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1847 raw2608; decide +kernel
    rw [heq]
    exact (canonical2608 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1847 (2 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1847 (2 : Fin 4) = raw2617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1847 raw2617; decide +kernel
    rw [heq]
    exact (canonical2617 hH).trans (sound842 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1847 (3 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1847 (3 : Fin 4) = raw2618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1847 raw2618; decide +kernel
    rw [heq]
    exact (canonical2618 hH).trans (sound1096 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1847 + (injectiveMoment H (mergeFirst pivotMatrix1847 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1847 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1847 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1847 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1847, value1078, value1096, value835, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1848 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1848 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound1848 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1848 = Sparse.eval value1848 (momentVector H) := by
  have heq : pivotMatrix1848 = (fun u v => node1848 (pivotPermutation1848 u) v) := by apply Matrix.ext; unfold pivotMatrix1848 node1848 pivotPermutation1848; decide +kernel
  have hmoment : injectiveMoment H node1848 = injectiveMoment H pivotMatrix1848 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1848 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1848 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1848 (0 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1848 (0 : Fin 4) = raw2494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1848 raw2494; decide +kernel
    rw [heq]
    exact (canonical2494 hH).trans (sound837 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1848 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1848 (1 : Fin 4) = raw2628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1848 raw2628; decide +kernel
    rw [heq]
    exact (canonical2628 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1848 (2 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1848 (2 : Fin 4) = raw2629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1848 raw2629; decide +kernel
    rw [heq]
    exact (canonical2629 hH).trans (sound844 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1848 (3 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1848 (3 : Fin 4) = raw2630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1848 raw2630; decide +kernel
    rw [heq]
    exact (canonical2630 hH).trans (sound1005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1848 + (injectiveMoment H (mergeFirst pivotMatrix1848 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1848 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1848 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1848 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1848, value1005, value1078, value837, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1849 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem sound1849 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1849 = Sparse.eval value1849 (momentVector H) := by
  have heq : pivotMatrix1849 = (fun u v => node1849 (pivotPermutation1849 u) v) := by apply Matrix.ext; unfold pivotMatrix1849 node1849 pivotPermutation1849; decide +kernel
  have hmoment : injectiveMoment H node1849 = injectiveMoment H pivotMatrix1849 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1849 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1849 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1849 (0 : Fin 5)) =
      Sparse.eval value863 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1849 (0 : Fin 5) = raw3895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1849 raw3895; decide +kernel
    rw [heq]
    exact (canonical3895 hH).trans (sound863 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1849 (1 : Fin 5)) =
      Sparse.eval value862 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1849 (1 : Fin 5) = raw2662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1849 raw2662; decide +kernel
    rw [heq]
    exact (canonical2662 hH).trans (sound862 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1849 (2 : Fin 5)) =
      Sparse.eval value525 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1849 (2 : Fin 5) = raw2654 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1849 raw2654; decide +kernel
    rw [heq]
    exact (canonical2654 hH).trans (sound525 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1849 (3 : Fin 5)) =
      Sparse.eval value855 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1849 (3 : Fin 5) = raw2651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1849 raw2651; decide +kernel
    rw [heq]
    exact (canonical2651 hH).trans (sound855 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1849 (4 : Fin 5)) =
      Sparse.eval value418 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1849 (4 : Fin 5) = raw2650 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1849 raw2650; decide +kernel
    rw [heq]
    exact (canonical2650 hH).trans (sound418 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1849 + (injectiveMoment H (mergeFirst pivotMatrix1849 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1849 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1849 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1849 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1849 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1849, value418, value525, value855, value862, value863, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1850 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem sound1850 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1850 = Sparse.eval value1850 (momentVector H) := by
  have heq : pivotMatrix1850 = (fun u v => node1850 (pivotPermutation1850 u) v) := by apply Matrix.ext; unfold pivotMatrix1850 node1850 pivotPermutation1850; decide +kernel
  have hmoment : injectiveMoment H node1850 = injectiveMoment H pivotMatrix1850 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1850 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1850 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1850 (0 : Fin 5)) =
      Sparse.eval value307 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1850 (0 : Fin 5) = raw271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1850 raw271; decide +kernel
    rw [heq]
    exact (canonical271 hH).trans (sound307 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1850 (1 : Fin 5)) =
      Sparse.eval value524 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1850 (1 : Fin 5) = raw2653 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1850 raw2653; decide +kernel
    rw [heq]
    exact (canonical2653 hH).trans (sound524 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1850 (2 : Fin 5)) =
      Sparse.eval value531 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1850 (2 : Fin 5) = raw2730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1850 raw2730; decide +kernel
    rw [heq]
    exact (canonical2730 hH).trans (sound531 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1850 (3 : Fin 5)) =
      Sparse.eval value556 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1850 (3 : Fin 5) = raw2745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1850 raw2745; decide +kernel
    rw [heq]
    exact (canonical2745 hH).trans (sound556 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1850 (4 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1850 (4 : Fin 5) = raw2749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1850 raw2749; decide +kernel
    rw [heq]
    exact (canonical2749 hH).trans (sound559 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1850 + (injectiveMoment H (mergeFirst pivotMatrix1850 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1850 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1850 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1850 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1850 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1850, value307, value524, value531, value556, value559, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1851 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem sound1851 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1851 = Sparse.eval value1851 (momentVector H) := by
  have heq : pivotMatrix1851 = (fun u v => node1851 (pivotPermutation1851 u) v) := by apply Matrix.ext; unfold pivotMatrix1851 node1851 pivotPermutation1851; decide +kernel
  have hmoment : injectiveMoment H node1851 = injectiveMoment H pivotMatrix1851 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1851 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1851 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1851 (0 : Fin 5)) =
      Sparse.eval value308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1851 (0 : Fin 5) = raw272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1851 raw272; decide +kernel
    rw [heq]
    exact (canonical272 hH).trans (sound308 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1851 (1 : Fin 5)) =
      Sparse.eval value526 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1851 (1 : Fin 5) = raw2656 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1851 raw2656; decide +kernel
    rw [heq]
    exact (canonical2656 hH).trans (sound526 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1851 (2 : Fin 5)) =
      Sparse.eval value535 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1851 (2 : Fin 5) = raw2732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1851 raw2732; decide +kernel
    rw [heq]
    exact (canonical2732 hH).trans (sound535 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1851 (3 : Fin 5)) =
      Sparse.eval value556 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1851 (3 : Fin 5) = raw2752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1851 raw2752; decide +kernel
    rw [heq]
    exact (canonical2752 hH).trans (sound556 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1851 (4 : Fin 5)) =
      Sparse.eval value561 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1851 (4 : Fin 5) = raw2755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1851 raw2755; decide +kernel
    rw [heq]
    exact (canonical2755 hH).trans (sound561 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1851 + (injectiveMoment H (mergeFirst pivotMatrix1851 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1851 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1851 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1851 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1851 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1851, value308, value526, value535, value556, value561, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1852 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem sound1852 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1852 = Sparse.eval value1852 (momentVector H) := by
  have heq : pivotMatrix1852 = (fun u v => node1852 (pivotPermutation1852 u) v) := by apply Matrix.ext; unfold pivotMatrix1852 node1852 pivotPermutation1852; decide +kernel
  have hmoment : injectiveMoment H node1852 = injectiveMoment H pivotMatrix1852 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1852 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1852 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1852 (0 : Fin 5)) =
      Sparse.eval value315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1852 (0 : Fin 5) = raw286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1852 raw286; decide +kernel
    rw [heq]
    exact (canonical286 hH).trans (sound315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1852 (1 : Fin 5)) =
      Sparse.eval value533 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1852 (1 : Fin 5) = raw2669 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1852 raw2669; decide +kernel
    rw [heq]
    exact (canonical2669 hH).trans (sound533 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1852 (2 : Fin 5)) =
      Sparse.eval value536 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1852 (2 : Fin 5) = raw2784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1852 raw2784; decide +kernel
    rw [heq]
    exact (canonical2784 hH).trans (sound536 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1852 (3 : Fin 5)) =
      Sparse.eval value542 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1852 (3 : Fin 5) = raw2804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1852 raw2804; decide +kernel
    rw [heq]
    exact (canonical2804 hH).trans (sound542 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1852 (4 : Fin 5)) =
      Sparse.eval value572 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1852 (4 : Fin 5) = raw2808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1852 raw2808; decide +kernel
    rw [heq]
    exact (canonical2808 hH).trans (sound572 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1852 + (injectiveMoment H (mergeFirst pivotMatrix1852 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1852 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1852 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1852 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1852 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1852, value315, value533, value536, value542, value572, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1853 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem sound1853 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1853 = Sparse.eval value1853 (momentVector H) := by
  have heq : pivotMatrix1853 = (fun u v => node1853 (pivotPermutation1853 u) v) := by apply Matrix.ext; unfold pivotMatrix1853 node1853 pivotPermutation1853; decide +kernel
  have hmoment : injectiveMoment H node1853 = injectiveMoment H pivotMatrix1853 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1853 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1853 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1853 (0 : Fin 5)) =
      Sparse.eval value317 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1853 (0 : Fin 5) = raw288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1853 raw288; decide +kernel
    rw [heq]
    exact (canonical288 hH).trans (sound317 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1853 (1 : Fin 5)) =
      Sparse.eval value369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1853 (1 : Fin 5) = raw2670 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1853 raw2670; decide +kernel
    rw [heq]
    exact (canonical2670 hH).trans (sound369 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1853 (2 : Fin 5)) =
      Sparse.eval value377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1853 (2 : Fin 5) = raw2785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1853 raw2785; decide +kernel
    rw [heq]
    exact (canonical2785 hH).trans (sound377 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1853 (3 : Fin 5)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1853 (3 : Fin 5) = raw2805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1853 raw2805; decide +kernel
    rw [heq]
    exact (canonical2805 hH).trans (sound177 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1853 (4 : Fin 5)) =
      Sparse.eval value572 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1853 (4 : Fin 5) = raw2810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1853 raw2810; decide +kernel
    rw [heq]
    exact (canonical2810 hH).trans (sound572 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1853 + (injectiveMoment H (mergeFirst pivotMatrix1853 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1853 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1853 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1853 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1853 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1853, value177, value317, value369, value377, value572, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1854 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem sound1854 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1854 = Sparse.eval value1854 (momentVector H) := by
  have heq : pivotMatrix1854 = (fun u v => node1854 (pivotPermutation1854 u) v) := by apply Matrix.ext; unfold pivotMatrix1854 node1854 pivotPermutation1854; decide +kernel
  have hmoment : injectiveMoment H node1854 = injectiveMoment H pivotMatrix1854 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1854 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1854 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1854 (0 : Fin 5)) =
      Sparse.eval value320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (0 : Fin 5) = raw293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw293; decide +kernel
    rw [heq]
    exact (canonical293 hH).trans (sound320 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1854 (1 : Fin 5)) =
      Sparse.eval value364 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (1 : Fin 5) = raw2671 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2671; decide +kernel
    rw [heq]
    exact (canonical2671 hH).trans (sound364 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1854 (2 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (2 : Fin 5) = raw2787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2787; decide +kernel
    rw [heq]
    exact (canonical2787 hH).trans (sound559 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1854 (3 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (3 : Fin 5) = raw2818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2818; decide +kernel
    rw [heq]
    exact (canonical2818 hH).trans (sound559 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1854 (4 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1854 (4 : Fin 5) = raw2819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1854 raw2819; decide +kernel
    rw [heq]
    exact (canonical2819 hH).trans (sound573 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1854 + (injectiveMoment H (mergeFirst pivotMatrix1854 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1854 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1854, value320, value364, value559, value573, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1855 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem sound1855 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1855 = Sparse.eval value1855 (momentVector H) := by
  have heq : pivotMatrix1855 = (fun u v => node1855 (pivotPermutation1855 u) v) := by apply Matrix.ext; unfold pivotMatrix1855 node1855 pivotPermutation1855; decide +kernel
  have hmoment : injectiveMoment H node1855 = injectiveMoment H pivotMatrix1855 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1855 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1855 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1855 (0 : Fin 5)) =
      Sparse.eval value321 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1855 (0 : Fin 5) = raw303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1855 raw303; decide +kernel
    rw [heq]
    exact (canonical303 hH).trans (sound321 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1855 (1 : Fin 5)) =
      Sparse.eval value539 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1855 (1 : Fin 5) = raw2685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1855 raw2685; decide +kernel
    rw [heq]
    exact (canonical2685 hH).trans (sound539 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1855 (2 : Fin 5)) =
      Sparse.eval value547 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1855 (2 : Fin 5) = raw2824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1855 raw2824; decide +kernel
    rw [heq]
    exact (canonical2824 hH).trans (sound547 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1855 (3 : Fin 5)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1855 (3 : Fin 5) = raw2836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1855 raw2836; decide +kernel
    rw [heq]
    exact (canonical2836 hH).trans (sound184 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1855 (4 : Fin 5)) =
      Sparse.eval value572 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1855 (4 : Fin 5) = raw2838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1855 raw2838; decide +kernel
    rw [heq]
    exact (canonical2838 hH).trans (sound572 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1855 + (injectiveMoment H (mergeFirst pivotMatrix1855 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1855 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1855 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1855 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1855 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1855, value184, value321, value539, value547, value572, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
