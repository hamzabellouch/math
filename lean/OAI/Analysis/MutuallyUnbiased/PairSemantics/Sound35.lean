import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical108
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical125
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical141
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical147
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical149
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical150
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2240 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2240 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem sound2240 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2240 = Sparse.eval value2240 (momentVector H) := by
  have heq : pivotMatrix2240 = (fun u v => node2240 (pivotPermutation2240 u) v) := by apply Matrix.ext; unfold pivotMatrix2240 node2240 pivotPermutation2240; decide +kernel
  have hmoment : injectiveMoment H node2240 = injectiveMoment H pivotMatrix2240 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2240 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2240 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2240 (0 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2240 (0 : Fin 4) = raw7214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2240 raw7214; decide +kernel
    rw [heq]
    exact (canonical7214 hH).trans (sound1263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2240 (1 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2240 (1 : Fin 4) = raw4636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2240 raw4636; decide +kernel
    rw [heq]
    exact (canonical4636 hH).trans (sound685 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2240 (2 : Fin 4)) =
      Sparse.eval value1346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2240 (2 : Fin 4) = raw4590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2240 raw4590; decide +kernel
    rw [heq]
    exact (canonical4590 hH).trans (sound1346 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2240 (3 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2240 (3 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2240 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2240 + (injectiveMoment H (mergeFirst pivotMatrix2240 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2240 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2240 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2240 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2240, value1263, value1346, value683, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2241 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2241 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

theorem sound2241 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2241 = Sparse.eval value2241 (momentVector H) := by
  have heq : pivotMatrix2241 = (fun u v => node2241 (pivotPermutation2241 u) v) := by apply Matrix.ext; unfold pivotMatrix2241 node2241 pivotPermutation2241; decide +kernel
  have hmoment : injectiveMoment H node2241 = injectiveMoment H pivotMatrix2241 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2241 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2241 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2241 (0 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2241 (0 : Fin 4) = raw5369 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2241 raw5369; decide +kernel
    rw [heq]
    exact (canonical5369 hH).trans (sound521 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2241 (1 : Fin 4)) =
      Sparse.eval value617 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2241 (1 : Fin 4) = raw4626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2241 raw4626; decide +kernel
    rw [heq]
    exact (canonical4626 hH).trans (sound617 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2241 (2 : Fin 4)) =
      Sparse.eval value1346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2241 (2 : Fin 4) = raw4589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2241 raw4589; decide +kernel
    rw [heq]
    exact (canonical4589 hH).trans (sound1346 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2241 (3 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2241 (3 : Fin 4) = raw4587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2241 raw4587; decide +kernel
    rw [heq]
    exact (canonical4587 hH).trans (sound520 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2241 + (injectiveMoment H (mergeFirst pivotMatrix2241 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2241 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2241 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2241 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2241, value1346, value520, value521, value617, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2242 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2242 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem sound2242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2242 = Sparse.eval value2242 (momentVector H) := by
  have heq : pivotMatrix2242 = (fun u v => node2242 (pivotPermutation2242 u) v) := by apply Matrix.ext; unfold pivotMatrix2242 node2242 pivotPermutation2242; decide +kernel
  have hmoment : injectiveMoment H node2242 = injectiveMoment H pivotMatrix2242 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2242 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2242 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2242 (0 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2242 (0 : Fin 4) = raw7219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2242 raw7219; decide +kernel
    rw [heq]
    exact (canonical7219 hH).trans (sound1267 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2242 (1 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2242 (1 : Fin 4) = raw4637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2242 raw4637; decide +kernel
    rw [heq]
    exact (canonical4637 hH).trans (sound1308 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2242 (2 : Fin 4)) =
      Sparse.eval value1015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2242 (2 : Fin 4) = raw4604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2242 raw4604; decide +kernel
    rw [heq]
    exact (canonical4604 hH).trans (sound1015 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2242 (3 : Fin 4)) =
      Sparse.eval value601 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2242 (3 : Fin 4) = raw4592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2242 raw4592; decide +kernel
    rw [heq]
    exact (canonical4592 hH).trans (sound601 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2242 + (injectiveMoment H (mergeFirst pivotMatrix2242 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2242 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2242 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2242 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2242, value1015, value1267, value1308, value601, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2243 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem sound2243 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2243 = Sparse.eval value2243 (momentVector H) := by
  have heq : pivotMatrix2243 = (fun u v => node2243 (pivotPermutation2243 u) v) := by apply Matrix.ext; unfold pivotMatrix2243 node2243 pivotPermutation2243; decide +kernel
  have hmoment : injectiveMoment H node2243 = injectiveMoment H pivotMatrix2243 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2243 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2243 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2243 (0 : Fin 4)) =
      Sparse.eval value1017 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2243 (0 : Fin 4) = raw5300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2243 raw5300; decide +kernel
    rw [heq]
    exact (canonical5300 hH).trans (sound1017 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2243 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2243 (1 : Fin 4) = raw4625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2243 raw4625; decide +kernel
    rw [heq]
    exact (canonical4625 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2243 (2 : Fin 4)) =
      Sparse.eval value937 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2243 (2 : Fin 4) = raw4602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2243 raw4602; decide +kernel
    rw [heq]
    exact (canonical4602 hH).trans (sound937 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2243 (3 : Fin 4)) =
      Sparse.eval value599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2243 (3 : Fin 4) = raw4600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2243 raw4600; decide +kernel
    rw [heq]
    exact (canonical4600 hH).trans (sound599 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2243 + (injectiveMoment H (mergeFirst pivotMatrix2243 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2243 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2243 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2243 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2243, value1016, value1017, value599, value937, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2244 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2244 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound2244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2244 = Sparse.eval value2244 (momentVector H) := by
  have heq : pivotMatrix2244 = (fun u v => node2244 (pivotPermutation2244 u) v) := by apply Matrix.ext; unfold pivotMatrix2244 node2244 pivotPermutation2244; decide +kernel
  have hmoment : injectiveMoment H node2244 = injectiveMoment H pivotMatrix2244 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2244 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2244 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2244 (0 : Fin 4)) =
      Sparse.eval value1012 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2244 (0 : Fin 4) = raw5301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2244 raw5301; decide +kernel
    rw [heq]
    exact (canonical5301 hH).trans (sound1012 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2244 (1 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2244 (1 : Fin 4) = raw4627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2244 raw4627; decide +kernel
    rw [heq]
    exact (canonical4627 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2244 (2 : Fin 4)) =
      Sparse.eval value1015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2244 (2 : Fin 4) = raw4604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2244 raw4604; decide +kernel
    rw [heq]
    exact (canonical4604 hH).trans (sound1015 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2244 (3 : Fin 4)) =
      Sparse.eval value937 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2244 (3 : Fin 4) = raw4602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2244 raw4602; decide +kernel
    rw [heq]
    exact (canonical4602 hH).trans (sound937 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2244 + (injectiveMoment H (mergeFirst pivotMatrix2244 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2244 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2244 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2244 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2244, value1012, value1013, value1015, value937, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2245 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2245 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem sound2245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2245 = Sparse.eval value2245 (momentVector H) := by
  have heq : pivotMatrix2245 = (fun u v => node2245 (pivotPermutation2245 u) v) := by apply Matrix.ext; unfold pivotMatrix2245 node2245 pivotPermutation2245; decide +kernel
  have hmoment : injectiveMoment H node2245 = injectiveMoment H pivotMatrix2245 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2245 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2245 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2245 (0 : Fin 4)) =
      Sparse.eval value989 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2245 (0 : Fin 4) = raw5373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2245 raw5373; decide +kernel
    rw [heq]
    exact (canonical5373 hH).trans (sound989 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2245 (1 : Fin 4)) =
      Sparse.eval value1089 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2245 (1 : Fin 4) = raw4630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2245 raw4630; decide +kernel
    rw [heq]
    exact (canonical4630 hH).trans (sound1089 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2245 (2 : Fin 4)) =
      Sparse.eval value1015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2245 (2 : Fin 4) = raw4604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2245 raw4604; decide +kernel
    rw [heq]
    exact (canonical4604 hH).trans (sound1015 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2245 (3 : Fin 4)) =
      Sparse.eval value1337 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2245 (3 : Fin 4) = raw4601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2245 raw4601; decide +kernel
    rw [heq]
    exact (canonical4601 hH).trans (sound1337 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2245 + (injectiveMoment H (mergeFirst pivotMatrix2245 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2245 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2245 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2245 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2245, value1015, value1089, value1337, value989, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2246 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2246 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem sound2246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2246 = Sparse.eval value2246 (momentVector H) := by
  have heq : pivotMatrix2246 = (fun u v => node2246 (pivotPermutation2246 u) v) := by apply Matrix.ext; unfold pivotMatrix2246 node2246 pivotPermutation2246; decide +kernel
  have hmoment : injectiveMoment H node2246 = injectiveMoment H pivotMatrix2246 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2246 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2246 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2246 (0 : Fin 4)) =
      Sparse.eval value720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2246 (0 : Fin 4) = raw5374 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2246 raw5374; decide +kernel
    rw [heq]
    exact (canonical5374 hH).trans (sound720 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2246 (1 : Fin 4)) =
      Sparse.eval value687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2246 (1 : Fin 4) = raw4631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2246 raw4631; decide +kernel
    rw [heq]
    exact (canonical4631 hH).trans (sound687 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2246 (2 : Fin 4)) =
      Sparse.eval value937 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2246 (2 : Fin 4) = raw4605 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2246 raw4605; decide +kernel
    rw [heq]
    exact (canonical4605 hH).trans (sound937 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2246 (3 : Fin 4)) =
      Sparse.eval value937 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2246 (3 : Fin 4) = raw4602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2246 raw4602; decide +kernel
    rw [heq]
    exact (canonical4602 hH).trans (sound937 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2246 + (injectiveMoment H (mergeFirst pivotMatrix2246 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2246 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2246 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2246 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2246, value687, value720, value937, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2247 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2247 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2247 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2247 = Sparse.eval value2247 (momentVector H) := by
  have heq : pivotMatrix2247 = (fun u v => node2247 (pivotPermutation2247 u) v) := by apply Matrix.ext; unfold pivotMatrix2247 node2247 pivotPermutation2247; decide +kernel
  have hmoment : injectiveMoment H node2247 = injectiveMoment H pivotMatrix2247 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2247 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2247 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2247 (0 : Fin 4)) =
      Sparse.eval value1154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2247 (0 : Fin 4) = raw5305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2247 raw5305; decide +kernel
    rw [heq]
    exact (canonical5305 hH).trans (sound1154 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2247 (1 : Fin 4)) =
      Sparse.eval value1356 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2247 (1 : Fin 4) = raw4723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2247 raw4723; decide +kernel
    rw [heq]
    exact (canonical4723 hH).trans (sound1356 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2247 (2 : Fin 4)) =
      Sparse.eval value1232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2247 (2 : Fin 4) = raw4656 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2247 raw4656; decide +kernel
    rw [heq]
    exact (canonical4656 hH).trans (sound1232 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2247 (3 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2247 (3 : Fin 4) = raw4655 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2247 raw4655; decide +kernel
    rw [heq]
    exact (canonical4655 hH).trans (sound1348 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2247 + (injectiveMoment H (mergeFirst pivotMatrix2247 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2247 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2247 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2247 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2247, value1154, value1232, value1348, value1356, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2248 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2248 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2248 = Sparse.eval value2248 (momentVector H) := by
  have heq : pivotMatrix2248 = (fun u v => node2248 (pivotPermutation2248 u) v) := by apply Matrix.ext; unfold pivotMatrix2248 node2248 pivotPermutation2248; decide +kernel
  have hmoment : injectiveMoment H node2248 = injectiveMoment H pivotMatrix2248 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2248 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2248 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2248 (0 : Fin 4)) =
      Sparse.eval value1167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2248 (0 : Fin 4) = raw7285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2248 raw7285; decide +kernel
    rw [heq]
    exact (canonical7285 hH).trans (sound1167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2248 (1 : Fin 4)) =
      Sparse.eval value1230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2248 (1 : Fin 4) = raw4851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2248 raw4851; decide +kernel
    rw [heq]
    exact (canonical4851 hH).trans (sound1230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2248 (2 : Fin 4)) =
      Sparse.eval value1232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2248 (2 : Fin 4) = raw4657 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2248 raw4657; decide +kernel
    rw [heq]
    exact (canonical4657 hH).trans (sound1232 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2248 (3 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2248 (3 : Fin 4) = raw4654 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2248 raw4654; decide +kernel
    rw [heq]
    exact (canonical4654 hH).trans (sound688 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2248 + (injectiveMoment H (mergeFirst pivotMatrix2248 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2248 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2248 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2248 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2248, value1167, value1230, value1232, value688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2249 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2249 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem sound2249 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2249 = Sparse.eval value2249 (momentVector H) := by
  have heq : pivotMatrix2249 = (fun u v => node2249 (pivotPermutation2249 u) v) := by apply Matrix.ext; unfold pivotMatrix2249 node2249 pivotPermutation2249; decide +kernel
  have hmoment : injectiveMoment H node2249 = injectiveMoment H pivotMatrix2249 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2249 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2249 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2249 (0 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2249 (0 : Fin 4) = raw7286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2249 raw7286; decide +kernel
    rw [heq]
    exact (canonical7286 hH).trans (sound1171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2249 (1 : Fin 4)) =
      Sparse.eval value586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2249 (1 : Fin 4) = raw4852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2249 raw4852; decide +kernel
    rw [heq]
    exact (canonical4852 hH).trans (sound586 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2249 (2 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2249 (2 : Fin 4) = raw4677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2249 raw4677; decide +kernel
    rw [heq]
    exact (canonical4677 hH).trans (sound1278 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2249 (3 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2249 (3 : Fin 4) = raw4663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2249 raw4663; decide +kernel
    rw [heq]
    exact (canonical4663 hH).trans (sound460 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2249 + (injectiveMoment H (mergeFirst pivotMatrix2249 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2249 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2249 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2249 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2249, value1171, value1278, value460, value586, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2250 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2250 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem sound2250 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2250 = Sparse.eval value2250 (momentVector H) := by
  have heq : pivotMatrix2250 = (fun u v => node2250 (pivotPermutation2250 u) v) := by apply Matrix.ext; unfold pivotMatrix2250 node2250 pivotPermutation2250; decide +kernel
  have hmoment : injectiveMoment H node2250 = injectiveMoment H pivotMatrix2250 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2250 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2250 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2250 (0 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2250 (0 : Fin 4) = raw5308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2250 raw5308; decide +kernel
    rw [heq]
    exact (canonical5308 hH).trans (sound453 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2250 (1 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2250 (1 : Fin 4) = raw4746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2250 raw4746; decide +kernel
    rw [heq]
    exact (canonical4746 hH).trans (sound1348 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2250 (2 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2250 (2 : Fin 4) = raw4677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2250 raw4677; decide +kernel
    rw [heq]
    exact (canonical4677 hH).trans (sound1278 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2250 (3 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2250 (3 : Fin 4) = raw4674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2250 raw4674; decide +kernel
    rw [heq]
    exact (canonical4674 hH).trans (sound454 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2250 + (injectiveMoment H (mergeFirst pivotMatrix2250 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2250 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2250 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2250 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2250, value1278, value1348, value453, value454, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2251 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2251 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound2251 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2251 = Sparse.eval value2251 (momentVector H) := by
  have heq : pivotMatrix2251 = (fun u v => node2251 (pivotPermutation2251 u) v) := by apply Matrix.ext; unfold pivotMatrix2251 node2251 pivotPermutation2251; decide +kernel
  have hmoment : injectiveMoment H node2251 = injectiveMoment H pivotMatrix2251 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2251 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2251 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2251 (0 : Fin 4)) =
      Sparse.eval value947 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2251 (0 : Fin 4) = raw5311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2251 raw5311; decide +kernel
    rw [heq]
    exact (canonical5311 hH).trans (sound947 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2251 (1 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2251 (1 : Fin 4) = raw4748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2251 raw4748; decide +kernel
    rw [heq]
    exact (canonical4748 hH).trans (sound803 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2251 (2 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2251 (2 : Fin 4) = raw4678 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2251 raw4678; decide +kernel
    rw [heq]
    exact (canonical4678 hH).trans (sound1003 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2251 (3 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2251 (3 : Fin 4) = raw4676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2251 raw4676; decide +kernel
    rw [heq]
    exact (canonical4676 hH).trans (sound495 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2251 + (injectiveMoment H (mergeFirst pivotMatrix2251 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2251 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2251 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2251 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2251, value1003, value495, value803, value947, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2252 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2252 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem sound2252 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2252 = Sparse.eval value2252 (momentVector H) := by
  have heq : pivotMatrix2252 = (fun u v => node2252 (pivotPermutation2252 u) v) := by apply Matrix.ext; unfold pivotMatrix2252 node2252 pivotPermutation2252; decide +kernel
  have hmoment : injectiveMoment H node2252 = injectiveMoment H pivotMatrix2252 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2252 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2252 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2252 (0 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2252 (0 : Fin 4) = raw7840 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2252 raw7840; decide +kernel
    rw [heq]
    exact (canonical7840 hH).trans (sound1341 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2252 (1 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2252 (1 : Fin 4) = raw4857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2252 raw4857; decide +kernel
    rw [heq]
    exact (canonical4857 hH).trans (sound693 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2252 (2 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2252 (2 : Fin 4) = raw4680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2252 raw4680; decide +kernel
    rw [heq]
    exact (canonical4680 hH).trans (sound454 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2252 (3 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2252 (3 : Fin 4) = raw4673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2252 raw4673; decide +kernel
    rw [heq]
    exact (canonical4673 hH).trans (sound468 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2252 + (injectiveMoment H (mergeFirst pivotMatrix2252 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2252 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2252 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2252 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2252, value1341, value454, value468, value693, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2253 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2253 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem sound2253 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2253 = Sparse.eval value2253 (momentVector H) := by
  have heq : pivotMatrix2253 = (fun u v => node2253 (pivotPermutation2253 u) v) := by apply Matrix.ext; unfold pivotMatrix2253 node2253 pivotPermutation2253; decide +kernel
  have hmoment : injectiveMoment H node2253 = injectiveMoment H pivotMatrix2253 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2253 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2253 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2253 (0 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2253 (0 : Fin 4) = raw7289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2253 raw7289; decide +kernel
    rw [heq]
    exact (canonical7289 hH).trans (sound1170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2253 (1 : Fin 4)) =
      Sparse.eval value596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2253 (1 : Fin 4) = raw4853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2253 raw4853; decide +kernel
    rw [heq]
    exact (canonical4853 hH).trans (sound596 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2253 (2 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2253 (2 : Fin 4) = raw4679 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2253 raw4679; decide +kernel
    rw [heq]
    exact (canonical4679 hH).trans (sound1278 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2253 (3 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2253 (3 : Fin 4) = raw4673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2253 raw4673; decide +kernel
    rw [heq]
    exact (canonical4673 hH).trans (sound468 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2253 + (injectiveMoment H (mergeFirst pivotMatrix2253 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2253 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2253 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2253 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2253, value1170, value1278, value468, value596, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2254 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2254 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

theorem sound2254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2254 = Sparse.eval value2254 (momentVector H) := by
  have heq : pivotMatrix2254 = (fun u v => node2254 (pivotPermutation2254 u) v) := by apply Matrix.ext; unfold pivotMatrix2254 node2254 pivotPermutation2254; decide +kernel
  have hmoment : injectiveMoment H node2254 = injectiveMoment H pivotMatrix2254 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2254 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2254 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2254 (0 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2254 (0 : Fin 4) = raw3474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2254 raw3474; decide +kernel
    rw [heq]
    exact (canonical3474 hH).trans (sound799 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2254 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2254 (1 : Fin 4) = raw4676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2254 raw4676; decide +kernel
    rw [heq]
    exact (canonical4676 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2254 (2 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2254 (2 : Fin 4) = raw4783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2254 raw4783; decide +kernel
    rw [heq]
    exact (canonical4783 hH).trans (sound815 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2254 (3 : Fin 4)) =
      Sparse.eval value800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2254 (3 : Fin 4) = raw4785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2254 raw4785; decide +kernel
    rw [heq]
    exact (canonical4785 hH).trans (sound800 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2254 + (injectiveMoment H (mergeFirst pivotMatrix2254 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2254 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2254 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2254 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2254, value495, value799, value800, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2255 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2255 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

theorem sound2255 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2255 = Sparse.eval value2255 (momentVector H) := by
  have heq : pivotMatrix2255 = (fun u v => node2255 (pivotPermutation2255 u) v) := by apply Matrix.ext; unfold pivotMatrix2255 node2255 pivotPermutation2255; decide +kernel
  have hmoment : injectiveMoment H node2255 = injectiveMoment H pivotMatrix2255 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2255 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2255 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2255 (0 : Fin 4)) =
      Sparse.eval value971 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2255 (0 : Fin 4) = raw3495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2255 raw3495; decide +kernel
    rw [heq]
    exact (canonical3495 hH).trans (sound971 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2255 (1 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2255 (1 : Fin 4) = raw4684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2255 raw4684; decide +kernel
    rw [heq]
    exact (canonical4684 hH).trans (sound1208 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2255 (2 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2255 (2 : Fin 4) = raw4802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2255 raw4802; decide +kernel
    rw [heq]
    exact (canonical4802 hH).trans (sound1208 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2255 (3 : Fin 4)) =
      Sparse.eval value1204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2255 (3 : Fin 4) = raw4804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2255 raw4804; decide +kernel
    rw [heq]
    exact (canonical4804 hH).trans (sound1204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2255 + (injectiveMoment H (mergeFirst pivotMatrix2255 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2255 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2255 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2255 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2255, value1204, value1208, value971, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2256 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2256 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

theorem sound2256 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2256 = Sparse.eval value2256 (momentVector H) := by
  have heq : pivotMatrix2256 = (fun u v => node2256 (pivotPermutation2256 u) v) := by apply Matrix.ext; unfold pivotMatrix2256 node2256 pivotPermutation2256; decide +kernel
  have hmoment : injectiveMoment H node2256 = injectiveMoment H pivotMatrix2256 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2256 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2256 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2256 (0 : Fin 4)) =
      Sparse.eval value911 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2256 (0 : Fin 4) = raw3758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2256 raw3758; decide +kernel
    rw [heq]
    exact (canonical3758 hH).trans (sound911 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2256 (1 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2256 (1 : Fin 4) = raw4682 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2256 raw4682; decide +kernel
    rw [heq]
    exact (canonical4682 hH).trans (sound917 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2256 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2256 (2 : Fin 4) = raw4782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2256 raw4782; decide +kernel
    rw [heq]
    exact (canonical4782 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2256 (3 : Fin 4)) =
      Sparse.eval value892 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2256 (3 : Fin 4) = raw4784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2256 raw4784; decide +kernel
    rw [heq]
    exact (canonical4784 hH).trans (sound892 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2256 + (injectiveMoment H (mergeFirst pivotMatrix2256 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2256 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2256 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2256 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2256, value892, value896, value911, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2257 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2257 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

theorem sound2257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2257 = Sparse.eval value2257 (momentVector H) := by
  have heq : pivotMatrix2257 = (fun u v => node2257 (pivotPermutation2257 u) v) := by apply Matrix.ext; unfold pivotMatrix2257 node2257 pivotPermutation2257; decide +kernel
  have hmoment : injectiveMoment H node2257 = injectiveMoment H pivotMatrix2257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2257 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2257 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2257 (0 : Fin 4)) =
      Sparse.eval value965 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2257 (0 : Fin 4) = raw3777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2257 raw3777; decide +kernel
    rw [heq]
    exact (canonical3777 hH).trans (sound965 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2257 (1 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2257 (1 : Fin 4) = raw4689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2257 raw4689; decide +kernel
    rw [heq]
    exact (canonical4689 hH).trans (sound604 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2257 (2 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2257 (2 : Fin 4) = raw4801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2257 raw4801; decide +kernel
    rw [heq]
    exact (canonical4801 hH).trans (sound1239 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2257 (3 : Fin 4)) =
      Sparse.eval value1200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2257 (3 : Fin 4) = raw4803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2257 raw4803; decide +kernel
    rw [heq]
    exact (canonical4803 hH).trans (sound1200 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2257 + (injectiveMoment H (mergeFirst pivotMatrix2257 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2257 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2257 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2257 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2257, value1200, value1239, value604, value965, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2258 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2258 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem sound2258 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2258 = Sparse.eval value2258 (momentVector H) := by
  have heq : pivotMatrix2258 = (fun u v => node2258 (pivotPermutation2258 u) v) := by apply Matrix.ext; unfold pivotMatrix2258 node2258 pivotPermutation2258; decide +kernel
  have hmoment : injectiveMoment H node2258 = injectiveMoment H pivotMatrix2258 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2258 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2258 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2258 (0 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2258 (0 : Fin 4) = raw3783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2258 raw3783; decide +kernel
    rw [heq]
    exact (canonical3783 hH).trans (sound1035 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2258 (1 : Fin 4)) =
      Sparse.eval value675 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2258 (1 : Fin 4) = raw4708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2258 raw4708; decide +kernel
    rw [heq]
    exact (canonical4708 hH).trans (sound675 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2258 (2 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2258 (2 : Fin 4) = raw4818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2258 raw4818; decide +kernel
    rw [heq]
    exact (canonical4818 hH).trans (sound408 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2258 (3 : Fin 4)) =
      Sparse.eval value1329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2258 (3 : Fin 4) = raw4819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2258 raw4819; decide +kernel
    rw [heq]
    exact (canonical4819 hH).trans (sound1329 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2258 + (injectiveMoment H (mergeFirst pivotMatrix2258 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2258 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2258 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2258 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2258, value1035, value1329, value408, value675, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2259 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2259 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

theorem sound2259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2259 = Sparse.eval value2259 (momentVector H) := by
  have heq : pivotMatrix2259 = (fun u v => node2259 (pivotPermutation2259 u) v) := by apply Matrix.ext; unfold pivotMatrix2259 node2259 pivotPermutation2259; decide +kernel
  have hmoment : injectiveMoment H node2259 = injectiveMoment H pivotMatrix2259 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2259 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2259 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2259 (0 : Fin 4)) =
      Sparse.eval value679 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2259 (0 : Fin 4) = raw4474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2259 raw4474; decide +kernel
    rw [heq]
    exact (canonical4474 hH).trans (sound679 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2259 (1 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2259 (1 : Fin 4) = raw4683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2259 raw4683; decide +kernel
    rw [heq]
    exact (canonical4683 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2259 (2 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2259 (2 : Fin 4) = raw4689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2259 raw4689; decide +kernel
    rw [heq]
    exact (canonical4689 hH).trans (sound604 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2259 (3 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2259 (3 : Fin 4) = raw4690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2259 raw4690; decide +kernel
    rw [heq]
    exact (canonical4690 hH).trans (sound510 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2259 + (injectiveMoment H (mergeFirst pivotMatrix2259 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2259 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2259 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2259 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2259, value1249, value510, value604, value679, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2260 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem sound2260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2260 = Sparse.eval value2260 (momentVector H) := by
  have heq : pivotMatrix2260 = (fun u v => node2260 (pivotPermutation2260 u) v) := by apply Matrix.ext; unfold pivotMatrix2260 node2260 pivotPermutation2260; decide +kernel
  have hmoment : injectiveMoment H node2260 = injectiveMoment H pivotMatrix2260 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2260 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2260 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2260 (0 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2260 (0 : Fin 4) = raw5019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2260 raw5019; decide +kernel
    rw [heq]
    exact (canonical5019 hH).trans (sound495 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2260 (1 : Fin 4)) =
      Sparse.eval value675 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2260 (1 : Fin 4) = raw4708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2260 raw4708; decide +kernel
    rw [heq]
    exact (canonical4708 hH).trans (sound675 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2260 (2 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2260 (2 : Fin 4) = raw4690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2260 raw4690; decide +kernel
    rw [heq]
    exact (canonical4690 hH).trans (sound510 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2260 (3 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2260 (3 : Fin 4) = raw4689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2260 raw4689; decide +kernel
    rw [heq]
    exact (canonical4689 hH).trans (sound604 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2260 + (injectiveMoment H (mergeFirst pivotMatrix2260 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2260 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2260 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2260 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2260, value495, value510, value604, value675, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2261 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2261 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 1, -1, -1]]

theorem sound2261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2261 = Sparse.eval value2261 (momentVector H) := by
  have heq : pivotMatrix2261 = (fun u v => node2261 (pivotPermutation2261 u) v) := by apply Matrix.ext; unfold pivotMatrix2261 node2261 pivotPermutation2261; decide +kernel
  have hmoment : injectiveMoment H node2261 = injectiveMoment H pivotMatrix2261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2261 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2261 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2261 (0 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2261 (0 : Fin 4) = raw7326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2261 raw7326; decide +kernel
    rw [heq]
    exact (canonical7326 hH).trans (sound1109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2261 (1 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2261 (1 : Fin 4) = raw4854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2261 raw4854; decide +kernel
    rw [heq]
    exact (canonical4854 hH).trans (sound484 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2261 (2 : Fin 4)) =
      Sparse.eval value690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2261 (2 : Fin 4) = raw4709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2261 raw4709; decide +kernel
    rw [heq]
    exact (canonical4709 hH).trans (sound690 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2261 (3 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2261 (3 : Fin 4) = raw4696 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2261 raw4696; decide +kernel
    rw [heq]
    exact (canonical4696 hH).trans (sound1223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2261 + (injectiveMoment H (mergeFirst pivotMatrix2261 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2261 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2261 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2261 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2261, value1109, value1223, value484, value690, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2262 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2262 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem sound2262 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2262 = Sparse.eval value2262 (momentVector H) := by
  have heq : pivotMatrix2262 = (fun u v => node2262 (pivotPermutation2262 u) v) := by apply Matrix.ext; unfold pivotMatrix2262 node2262 pivotPermutation2262; decide +kernel
  have hmoment : injectiveMoment H node2262 = injectiveMoment H pivotMatrix2262 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2262 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2262 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2262 (0 : Fin 4)) =
      Sparse.eval value1201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2262 (0 : Fin 4) = raw7327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2262 raw7327; decide +kernel
    rw [heq]
    exact (canonical7327 hH).trans (sound1201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2262 (1 : Fin 4)) =
      Sparse.eval value1369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2262 (1 : Fin 4) = raw4855 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2262 raw4855; decide +kernel
    rw [heq]
    exact (canonical4855 hH).trans (sound1369 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2262 (2 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2262 (2 : Fin 4) = raw4712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2262 raw4712; decide +kernel
    rw [heq]
    exact (canonical4712 hH).trans (sound1231 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2262 (3 : Fin 4)) =
      Sparse.eval value689 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2262 (3 : Fin 4) = raw4698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2262 raw4698; decide +kernel
    rw [heq]
    exact (canonical4698 hH).trans (sound689 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2262 + (injectiveMoment H (mergeFirst pivotMatrix2262 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2262 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2262 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2262 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2262, value1201, value1231, value1369, value689, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2263 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2263 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1]]

theorem sound2263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2263 = Sparse.eval value2263 (momentVector H) := by
  have heq : pivotMatrix2263 = (fun u v => node2263 (pivotPermutation2263 u) v) := by apply Matrix.ext; unfold pivotMatrix2263 node2263 pivotPermutation2263; decide +kernel
  have hmoment : injectiveMoment H node2263 = injectiveMoment H pivotMatrix2263 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2263 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2263 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2263 (0 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2263 (0 : Fin 4) = raw7898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2263 raw7898; decide +kernel
    rw [heq]
    exact (canonical7898 hH).trans (sound1099 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2263 (1 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2263 (1 : Fin 4) = raw4858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2263 raw4858; decide +kernel
    rw [heq]
    exact (canonical4858 hH).trans (sound487 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2263 (2 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2263 (2 : Fin 4) = raw4716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2263 raw4716; decide +kernel
    rw [heq]
    exact (canonical4716 hH).trans (sound490 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2263 (3 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2263 (3 : Fin 4) = raw4701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2263 raw4701; decide +kernel
    rw [heq]
    exact (canonical4701 hH).trans (sound476 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2263 + (injectiveMoment H (mergeFirst pivotMatrix2263 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2263 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2263 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2263 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2263, value1099, value476, value487, value490, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2264 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2264 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

theorem sound2264 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2264 = Sparse.eval value2264 (momentVector H) := by
  have heq : pivotMatrix2264 = (fun u v => node2264 (pivotPermutation2264 u) v) := by apply Matrix.ext; unfold pivotMatrix2264 node2264 pivotPermutation2264; decide +kernel
  have hmoment : injectiveMoment H node2264 = injectiveMoment H pivotMatrix2264 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2264 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2264 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2264 (0 : Fin 4)) =
      Sparse.eval value824 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2264 (0 : Fin 4) = raw5313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2264 raw5313; decide +kernel
    rw [heq]
    exact (canonical5313 hH).trans (sound824 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2264 (1 : Fin 4)) =
      Sparse.eval value840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2264 (1 : Fin 4) = raw4820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2264 raw4820; decide +kernel
    rw [heq]
    exact (canonical4820 hH).trans (sound840 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2264 (2 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2264 (2 : Fin 4) = raw4712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2264 raw4712; decide +kernel
    rw [heq]
    exact (canonical4712 hH).trans (sound1231 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2264 (3 : Fin 4)) =
      Sparse.eval value690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2264 (3 : Fin 4) = raw4709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2264 raw4709; decide +kernel
    rw [heq]
    exact (canonical4709 hH).trans (sound690 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2264 + (injectiveMoment H (mergeFirst pivotMatrix2264 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2264 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2264 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2264 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2264, value1231, value690, value824, value840, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2265 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2265 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 0, -1, 0]]

theorem sound2265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2265 = Sparse.eval value2265 (momentVector H) := by
  have heq : pivotMatrix2265 = (fun u v => node2265 (pivotPermutation2265 u) v) := by apply Matrix.ext; unfold pivotMatrix2265 node2265 pivotPermutation2265; decide +kernel
  have hmoment : injectiveMoment H node2265 = injectiveMoment H pivotMatrix2265 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2265 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2265 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2265 (0 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2265 (0 : Fin 4) = raw5411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2265 raw5411; decide +kernel
    rw [heq]
    exact (canonical5411 hH).trans (sound1223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2265 (1 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2265 (1 : Fin 4) = raw4826 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2265 raw4826; decide +kernel
    rw [heq]
    exact (canonical4826 hH).trans (sound1231 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2265 (2 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2265 (2 : Fin 4) = raw4713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2265 raw4713; decide +kernel
    rw [heq]
    exact (canonical4713 hH).trans (sound801 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2265 (3 : Fin 4)) =
      Sparse.eval value690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2265 (3 : Fin 4) = raw4709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2265 raw4709; decide +kernel
    rw [heq]
    exact (canonical4709 hH).trans (sound690 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2265 + (injectiveMoment H (mergeFirst pivotMatrix2265 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2265 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2265 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2265 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2265, value1223, value1231, value690, value801, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2266 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2266 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]

theorem sound2266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2266 = Sparse.eval value2266 (momentVector H) := by
  have heq : pivotMatrix2266 = (fun u v => node2266 (pivotPermutation2266 u) v) := by apply Matrix.ext; unfold pivotMatrix2266 node2266 pivotPermutation2266; decide +kernel
  have hmoment : injectiveMoment H node2266 = injectiveMoment H pivotMatrix2266 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2266 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2266 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2266 (0 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2266 (0 : Fin 4) = raw5412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2266 raw5412; decide +kernel
    rw [heq]
    exact (canonical5412 hH).trans (sound476 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2266 (1 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2266 (1 : Fin 4) = raw4827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2266 raw4827; decide +kernel
    rw [heq]
    exact (canonical4827 hH).trans (sound1352 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2266 (2 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2266 (2 : Fin 4) = raw4714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2266 raw4714; decide +kernel
    rw [heq]
    exact (canonical4714 hH).trans (sound801 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2266 (3 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2266 (3 : Fin 4) = raw4710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2266 raw4710; decide +kernel
    rw [heq]
    exact (canonical4710 hH).trans (sound490 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2266 + (injectiveMoment H (mergeFirst pivotMatrix2266 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2266 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2266 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2266 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2266, value1352, value476, value490, value801, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2267 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2267 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -3, 2]]

theorem sound2267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2267 = Sparse.eval value2267 (momentVector H) := by
  have heq : pivotMatrix2267 = (fun u v => node2267 (pivotPermutation2267 u) v) := by apply Matrix.ext; unfold pivotMatrix2267 node2267 pivotPermutation2267; decide +kernel
  have hmoment : injectiveMoment H node2267 = injectiveMoment H pivotMatrix2267 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2267 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2267 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2267 (0 : Fin 4)) =
      Sparse.eval value1374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2267 (0 : Fin 4) = raw5413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2267 raw5413; decide +kernel
    rw [heq]
    exact (canonical5413 hH).trans (sound1374 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2267 (1 : Fin 4)) =
      Sparse.eval value1355 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2267 (1 : Fin 4) = raw4828 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2267 raw4828; decide +kernel
    rw [heq]
    exact (canonical4828 hH).trans (sound1355 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2267 (2 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2267 (2 : Fin 4) = raw4715 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2267 raw4715; decide +kernel
    rw [heq]
    exact (canonical4715 hH).trans (sound1231 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2267 (3 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2267 (3 : Fin 4) = raw4711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2267 raw4711; decide +kernel
    rw [heq]
    exact (canonical4711 hH).trans (sound1352 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2267 + (injectiveMoment H (mergeFirst pivotMatrix2267 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2267 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2267 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2267 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2267, value1231, value1352, value1355, value1374, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2268 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2268 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound2268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2268 = Sparse.eval value2268 (momentVector H) := by
  have heq : pivotMatrix2268 = (fun u v => node2268 (pivotPermutation2268 u) v) := by apply Matrix.ext; unfold pivotMatrix2268 node2268 pivotPermutation2268; decide +kernel
  have hmoment : injectiveMoment H node2268 = injectiveMoment H pivotMatrix2268 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2268 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2268 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2268 (0 : Fin 4)) =
      Sparse.eval value1017 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2268 (0 : Fin 4) = raw5020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2268 raw5020; decide +kernel
    rw [heq]
    exact (canonical5020 hH).trans (sound1017 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2268 (1 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2268 (1 : Fin 4) = raw4736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2268 raw4736; decide +kernel
    rw [heq]
    exact (canonical4736 hH).trans (sound1059 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2268 (2 : Fin 4)) =
      Sparse.eval value611 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2268 (2 : Fin 4) = raw4719 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2268 raw4719; decide +kernel
    rw [heq]
    exact (canonical4719 hH).trans (sound611 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2268 (3 : Fin 4)) =
      Sparse.eval value1068 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2268 (3 : Fin 4) = raw4718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2268 raw4718; decide +kernel
    rw [heq]
    exact (canonical4718 hH).trans (sound1068 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2268 + (injectiveMoment H (mergeFirst pivotMatrix2268 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2268 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2268 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2268 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2268, value1017, value1059, value1068, value611, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2269 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2269 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2269 = Sparse.eval value2269 (momentVector H) := by
  have heq : pivotMatrix2269 = (fun u v => node2269 (pivotPermutation2269 u) v) := by apply Matrix.ext; unfold pivotMatrix2269 node2269 pivotPermutation2269; decide +kernel
  have hmoment : injectiveMoment H node2269 = injectiveMoment H pivotMatrix2269 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2269 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2269 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2269 (0 : Fin 4)) =
      Sparse.eval value1181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2269 (0 : Fin 4) = raw7328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2269 raw7328; decide +kernel
    rw [heq]
    exact (canonical7328 hH).trans (sound1181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2269 (1 : Fin 4)) =
      Sparse.eval value1343 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2269 (1 : Fin 4) = raw4856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2269 raw4856; decide +kernel
    rw [heq]
    exact (canonical4856 hH).trans (sound1343 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2269 (2 : Fin 4)) =
      Sparse.eval value1356 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2269 (2 : Fin 4) = raw4724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2269 raw4724; decide +kernel
    rw [heq]
    exact (canonical4724 hH).trans (sound1356 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2269 (3 : Fin 4)) =
      Sparse.eval value691 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2269 (3 : Fin 4) = raw4721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2269 raw4721; decide +kernel
    rw [heq]
    exact (canonical4721 hH).trans (sound691 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2269 + (injectiveMoment H (mergeFirst pivotMatrix2269 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2269 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2269 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2269 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2269, value1181, value1343, value1356, value691, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2270 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2270 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem sound2270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2270 = Sparse.eval value2270 (momentVector H) := by
  have heq : pivotMatrix2270 = (fun u v => node2270 (pivotPermutation2270 u) v) := by apply Matrix.ext; unfold pivotMatrix2270 node2270 pivotPermutation2270; decide +kernel
  have hmoment : injectiveMoment H node2270 = injectiveMoment H pivotMatrix2270 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2270 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2270 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2270 (0 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (0 : Fin 4) = raw4498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4498; decide +kernel
    rw [heq]
    exact (canonical4498 hH).trans (sound576 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2270 (1 : Fin 4)) =
      Sparse.eval value691 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (1 : Fin 4) = raw4721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4721; decide +kernel
    rw [heq]
    exact (canonical4721 hH).trans (sound691 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2270 (2 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (2 : Fin 4) = raw4739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4739; decide +kernel
    rw [heq]
    exact (canonical4739 hH).trans (sound472 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2270 (3 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2270 (3 : Fin 4) = raw4742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2270 raw4742; decide +kernel
    rw [heq]
    exact (canonical4742 hH).trans (sound448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2270 + (injectiveMoment H (mergeFirst pivotMatrix2270 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2270 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2270 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2270 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2270, value448, value472, value576, value691, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2271 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2271 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem sound2271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2271 = Sparse.eval value2271 (momentVector H) := by
  have heq : pivotMatrix2271 = (fun u v => node2271 (pivotPermutation2271 u) v) := by apply Matrix.ext; unfold pivotMatrix2271 node2271 pivotPermutation2271; decide +kernel
  have hmoment : injectiveMoment H node2271 = injectiveMoment H pivotMatrix2271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2271 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2271 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2271 (0 : Fin 4)) =
      Sparse.eval value579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (0 : Fin 4) = raw4499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4499; decide +kernel
    rw [heq]
    exact (canonical4499 hH).trans (sound579 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2271 (1 : Fin 4)) =
      Sparse.eval value692 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (1 : Fin 4) = raw4722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4722; decide +kernel
    rw [heq]
    exact (canonical4722 hH).trans (sound692 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2271 (2 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (2 : Fin 4) = raw4743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4743; decide +kernel
    rw [heq]
    exact (canonical4743 hH).trans (sound449 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2271 (3 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (3 : Fin 4) = raw4744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4744; decide +kernel
    rw [heq]
    exact (canonical4744 hH).trans (sound473 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2271 + (injectiveMoment H (mergeFirst pivotMatrix2271 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2271 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2271 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2271 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2271, value449, value473, value579, value692, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2272 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2272 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem sound2272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2272 = Sparse.eval value2272 (momentVector H) := by
  have heq : pivotMatrix2272 = (fun u v => node2272 (pivotPermutation2272 u) v) := by apply Matrix.ext; unfold pivotMatrix2272 node2272 pivotPermutation2272; decide +kernel
  have hmoment : injectiveMoment H node2272 = injectiveMoment H pivotMatrix2272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2272 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2272 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2272 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2272 (0 : Fin 4) = raw5021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2272 raw5021; decide +kernel
    rw [heq]
    exact (canonical5021 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2272 (1 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2272 (1 : Fin 4) = raw4775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2272 raw4775; decide +kernel
    rw [heq]
    exact (canonical4775 hH).trans (sound1033 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2272 (2 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2272 (2 : Fin 4) = raw4736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2272 raw4736; decide +kernel
    rw [heq]
    exact (canonical4736 hH).trans (sound1059 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2272 (3 : Fin 4)) =
      Sparse.eval value794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2272 (3 : Fin 4) = raw4734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2272 raw4734; decide +kernel
    rw [heq]
    exact (canonical4734 hH).trans (sound794 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2272 + (injectiveMoment H (mergeFirst pivotMatrix2272 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2272 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2272 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2272 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2272, value1033, value1059, value794, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2273 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2273 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]

theorem sound2273 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2273 = Sparse.eval value2273 (momentVector H) := by
  have heq : pivotMatrix2273 = (fun u v => node2273 (pivotPermutation2273 u) v) := by apply Matrix.ext; unfold pivotMatrix2273 node2273 pivotPermutation2273; decide +kernel
  have hmoment : injectiveMoment H node2273 = injectiveMoment H pivotMatrix2273 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2273 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2273 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2273 (0 : Fin 4)) =
      Sparse.eval value719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2273 (0 : Fin 4) = raw5323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2273 raw5323; decide +kernel
    rw [heq]
    exact (canonical5323 hH).trans (sound719 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2273 (1 : Fin 4)) =
      Sparse.eval value588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2273 (1 : Fin 4) = raw4830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2273 raw4830; decide +kernel
    rw [heq]
    exact (canonical4830 hH).trans (sound588 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2273 (2 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2273 (2 : Fin 4) = raw4737 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2273 raw4737; decide +kernel
    rw [heq]
    exact (canonical4737 hH).trans (sound521 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2273 (3 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2273 (3 : Fin 4) = raw4731 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2273 raw4731; decide +kernel
    rw [heq]
    exact (canonical4731 hH).trans (sound1304 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2273 + (injectiveMoment H (mergeFirst pivotMatrix2273 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2273 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2273 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2273 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2273, value1304, value521, value588, value719, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2274 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2274 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem sound2274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2274 = Sparse.eval value2274 (momentVector H) := by
  have heq : pivotMatrix2274 = (fun u v => node2274 (pivotPermutation2274 u) v) := by apply Matrix.ext; unfold pivotMatrix2274 node2274 pivotPermutation2274; decide +kernel
  have hmoment : injectiveMoment H node2274 = injectiveMoment H pivotMatrix2274 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2274 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2274 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2274 (0 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2274 (0 : Fin 4) = raw5326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2274 raw5326; decide +kernel
    rw [heq]
    exact (canonical5326 hH).trans (sound448 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2274 (1 : Fin 4)) =
      Sparse.eval value692 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2274 (1 : Fin 4) = raw4831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2274 raw4831; decide +kernel
    rw [heq]
    exact (canonical4831 hH).trans (sound692 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2274 (2 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2274 (2 : Fin 4) = raw4746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2274 raw4746; decide +kernel
    rw [heq]
    exact (canonical4746 hH).trans (sound1348 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2274 (3 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2274 (3 : Fin 4) = raw4743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2274 raw4743; decide +kernel
    rw [heq]
    exact (canonical4743 hH).trans (sound449 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2274 + (injectiveMoment H (mergeFirst pivotMatrix2274 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2274 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2274 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2274 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2274, value1348, value448, value449, value692, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2275 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2275 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound2275 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2275 = Sparse.eval value2275 (momentVector H) := by
  have heq : pivotMatrix2275 = (fun u v => node2275 (pivotPermutation2275 u) v) := by apply Matrix.ext; unfold pivotMatrix2275 node2275 pivotPermutation2275; decide +kernel
  have hmoment : injectiveMoment H node2275 = injectiveMoment H pivotMatrix2275 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2275 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2275 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2275 (0 : Fin 4)) =
      Sparse.eval value1303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2275 (0 : Fin 4) = raw5330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2275 raw5330; decide +kernel
    rw [heq]
    exact (canonical5330 hH).trans (sound1303 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2275 (1 : Fin 4)) =
      Sparse.eval value1365 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2275 (1 : Fin 4) = raw4833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2275 raw4833; decide +kernel
    rw [heq]
    exact (canonical4833 hH).trans (sound1365 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2275 (2 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2275 (2 : Fin 4) = raw4749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2275 raw4749; decide +kernel
    rw [heq]
    exact (canonical4749 hH).trans (sound803 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2275 (3 : Fin 4)) =
      Sparse.eval value1296 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2275 (3 : Fin 4) = raw4747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2275 raw4747; decide +kernel
    rw [heq]
    exact (canonical4747 hH).trans (sound1296 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2275 + (injectiveMoment H (mergeFirst pivotMatrix2275 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2275 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2275 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2275 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2275, value1296, value1303, value1365, value803, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2276 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2276 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem sound2276 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2276 = Sparse.eval value2276 (momentVector H) := by
  have heq : pivotMatrix2276 = (fun u v => node2276 (pivotPermutation2276 u) v) := by apply Matrix.ext; unfold pivotMatrix2276 node2276 pivotPermutation2276; decide +kernel
  have hmoment : injectiveMoment H node2276 = injectiveMoment H pivotMatrix2276 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2276 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2276 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2276 (0 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2276 (0 : Fin 4) = raw7331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2276 raw7331; decide +kernel
    rw [heq]
    exact (canonical7331 hH).trans (sound1177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2276 (1 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2276 (1 : Fin 4) = raw4857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2276 raw4857; decide +kernel
    rw [heq]
    exact (canonical4857 hH).trans (sound693 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2276 (2 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2276 (2 : Fin 4) = raw4750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2276 raw4750; decide +kernel
    rw [heq]
    exact (canonical4750 hH).trans (sound1348 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2276 (3 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2276 (3 : Fin 4) = raw4742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2276 raw4742; decide +kernel
    rw [heq]
    exact (canonical4742 hH).trans (sound448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2276 + (injectiveMoment H (mergeFirst pivotMatrix2276 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2276 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2276 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2276 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2276, value1177, value1348, value448, value693, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2277 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2277 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

theorem sound2277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2277 = Sparse.eval value2277 (momentVector H) := by
  have heq : pivotMatrix2277 = (fun u v => node2277 (pivotPermutation2277 u) v) := by apply Matrix.ext; unfold pivotMatrix2277 node2277 pivotPermutation2277; decide +kernel
  have hmoment : injectiveMoment H node2277 = injectiveMoment H pivotMatrix2277 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2277 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2277 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2277 (0 : Fin 4)) =
      Sparse.eval value958 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2277 (0 : Fin 4) = raw4527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2277 raw4527; decide +kernel
    rw [heq]
    exact (canonical4527 hH).trans (sound958 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2277 (1 : Fin 4)) =
      Sparse.eval value794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2277 (1 : Fin 4) = raw4734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2277 raw4734; decide +kernel
    rw [heq]
    exact (canonical4734 hH).trans (sound794 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2277 (2 : Fin 4)) =
      Sparse.eval value790 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2277 (2 : Fin 4) = raw4768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2277 raw4768; decide +kernel
    rw [heq]
    exact (canonical4768 hH).trans (sound790 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2277 (3 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2277 (3 : Fin 4) = raw4775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2277 raw4775; decide +kernel
    rw [heq]
    exact (canonical4775 hH).trans (sound1033 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2277 + (injectiveMoment H (mergeFirst pivotMatrix2277 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2277 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2277 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2277 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2277, value1033, value790, value794, value958, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2278 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2278 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

theorem sound2278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2278 = Sparse.eval value2278 (momentVector H) := by
  have heq : pivotMatrix2278 = (fun u v => node2278 (pivotPermutation2278 u) v) := by apply Matrix.ext; unfold pivotMatrix2278 node2278 pivotPermutation2278; decide +kernel
  have hmoment : injectiveMoment H node2278 = injectiveMoment H pivotMatrix2278 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2278 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2278 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2278 (0 : Fin 4)) =
      Sparse.eval value757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (0 : Fin 4) = raw4534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4534; decide +kernel
    rw [heq]
    exact (canonical4534 hH).trans (sound757 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2278 (1 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (1 : Fin 4) = raw4742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4742; decide +kernel
    rw [heq]
    exact (canonical4742 hH).trans (sound448 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2278 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (2 : Fin 4) = raw4777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4777; decide +kernel
    rw [heq]
    exact (canonical4777 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2278 (3 : Fin 4)) =
      Sparse.eval value895 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2278 (3 : Fin 4) = raw4781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2278 raw4781; decide +kernel
    rw [heq]
    exact (canonical4781 hH).trans (sound895 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2278 + (injectiveMoment H (mergeFirst pivotMatrix2278 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2278 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2278 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2278 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2278, value448, value757, value895, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2279 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2279 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

theorem sound2279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2279 = Sparse.eval value2279 (momentVector H) := by
  have heq : pivotMatrix2279 = (fun u v => node2279 (pivotPermutation2279 u) v) := by apply Matrix.ext; unfold pivotMatrix2279 node2279 pivotPermutation2279; decide +kernel
  have hmoment : injectiveMoment H node2279 = injectiveMoment H pivotMatrix2279 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2279 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2279 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2279 (0 : Fin 4)) =
      Sparse.eval value1370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2279 (0 : Fin 4) = raw4560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2279 raw4560; decide +kernel
    rw [heq]
    exact (canonical4560 hH).trans (sound1370 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2279 (1 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2279 (1 : Fin 4) = raw4786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2279 raw4786; decide +kernel
    rw [heq]
    exact (canonical4786 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2279 (2 : Fin 4)) =
      Sparse.eval value1319 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2279 (2 : Fin 4) = raw4793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2279 raw4793; decide +kernel
    rw [heq]
    exact (canonical4793 hH).trans (sound1319 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2279 (3 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2279 (3 : Fin 4) = raw4795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2279 raw4795; decide +kernel
    rw [heq]
    exact (canonical4795 hH).trans (sound1309 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2279 + (injectiveMoment H (mergeFirst pivotMatrix2279 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2279 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2279 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2279 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2279, value1309, value1319, value1370, value202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2280 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2280 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

theorem sound2280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2280 = Sparse.eval value2280 (momentVector H) := by
  have heq : pivotMatrix2280 = (fun u v => node2280 (pivotPermutation2280 u) v) := by apply Matrix.ext; unfold pivotMatrix2280 node2280 pivotPermutation2280; decide +kernel
  have hmoment : injectiveMoment H node2280 = injectiveMoment H pivotMatrix2280 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2280 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2280 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2280 (0 : Fin 4)) =
      Sparse.eval value728 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2280 (0 : Fin 4) = raw4570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2280 raw4570; decide +kernel
    rw [heq]
    exact (canonical4570 hH).trans (sound728 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2280 (1 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2280 (1 : Fin 4) = raw4787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2280 raw4787; decide +kernel
    rw [heq]
    exact (canonical4787 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2280 (2 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2280 (2 : Fin 4) = raw4799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2280 raw4799; decide +kernel
    rw [heq]
    exact (canonical4799 hH).trans (sound828 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2280 (3 : Fin 4)) =
      Sparse.eval value1196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2280 (3 : Fin 4) = raw4800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2280 raw4800; decide +kernel
    rw [heq]
    exact (canonical4800 hH).trans (sound1196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2280 + (injectiveMoment H (mergeFirst pivotMatrix2280 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2280 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2280 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2280 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2280, value1196, value212, value728, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2281 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2281 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem sound2281 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2281 = Sparse.eval value2281 (momentVector H) := by
  have heq : pivotMatrix2281 = (fun u v => node2281 (pivotPermutation2281 u) v) := by apply Matrix.ext; unfold pivotMatrix2281 node2281 pivotPermutation2281; decide +kernel
  have hmoment : injectiveMoment H node2281 = injectiveMoment H pivotMatrix2281 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2281 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2281 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2281 (0 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2281 (0 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2281 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2281 (1 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2281 (1 : Fin 4) = raw4795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2281 raw4795; decide +kernel
    rw [heq]
    exact (canonical4795 hH).trans (sound1309 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2281 (2 : Fin 4)) =
      Sparse.eval value588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2281 (2 : Fin 4) = raw4808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2281 raw4808; decide +kernel
    rw [heq]
    exact (canonical4808 hH).trans (sound588 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2281 (3 : Fin 4)) =
      Sparse.eval value606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2281 (3 : Fin 4) = raw4810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2281 raw4810; decide +kernel
    rw [heq]
    exact (canonical4810 hH).trans (sound606 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2281 + (injectiveMoment H (mergeFirst pivotMatrix2281 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2281 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2281 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2281 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2281, value1309, value588, value606, value683, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2282 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2282 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

theorem sound2282 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2282 = Sparse.eval value2282 (momentVector H) := by
  have heq : pivotMatrix2282 = (fun u v => node2282 (pivotPermutation2282 u) v) := by apply Matrix.ext; unfold pivotMatrix2282 node2282 pivotPermutation2282; decide +kernel
  have hmoment : injectiveMoment H node2282 = injectiveMoment H pivotMatrix2282 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2282 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2282 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2282 (0 : Fin 4)) =
      Sparse.eval value410 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2282 (0 : Fin 4) = raw4585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2282 raw4585; decide +kernel
    rw [heq]
    exact (canonical4585 hH).trans (sound410 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2282 (1 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2282 (1 : Fin 4) = raw4799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2282 raw4799; decide +kernel
    rw [heq]
    exact (canonical4799 hH).trans (sound828 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2282 (2 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2282 (2 : Fin 4) = raw4816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2282 raw4816; decide +kernel
    rw [heq]
    exact (canonical4816 hH).trans (sound831 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2282 (3 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2282 (3 : Fin 4) = raw4817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2282 raw4817; decide +kernel
    rw [heq]
    exact (canonical4817 hH).trans (sound405 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2282 + (injectiveMoment H (mergeFirst pivotMatrix2282 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2282 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2282 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2282 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2282, value405, value410, value828, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2283 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2283 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem sound2283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2283 = Sparse.eval value2283 (momentVector H) := by
  have heq : pivotMatrix2283 = (fun u v => node2283 (pivotPermutation2283 u) v) := by apply Matrix.ext; unfold pivotMatrix2283 node2283 pivotPermutation2283; decide +kernel
  have hmoment : injectiveMoment H node2283 = injectiveMoment H pivotMatrix2283 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2283 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2283 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2283 (0 : Fin 4)) =
      Sparse.eval value596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2283 (0 : Fin 4) = raw4607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2283 raw4607; decide +kernel
    rw [heq]
    exact (canonical4607 hH).trans (sound596 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2283 (1 : Fin 4)) =
      Sparse.eval value692 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2283 (1 : Fin 4) = raw4831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2283 raw4831; decide +kernel
    rw [heq]
    exact (canonical4831 hH).trans (sound692 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2283 (2 : Fin 4)) =
      Sparse.eval value586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2283 (2 : Fin 4) = raw4834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2283 raw4834; decide +kernel
    rw [heq]
    exact (canonical4834 hH).trans (sound586 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2283 (3 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2283 (3 : Fin 4) = raw4835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2283 raw4835; decide +kernel
    rw [heq]
    exact (canonical4835 hH).trans (sound473 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2283 + (injectiveMoment H (mergeFirst pivotMatrix2283 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2283 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2283 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2283 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2283, value473, value586, value596, value692, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2284 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2284 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound2284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2284 = Sparse.eval value2284 (momentVector H) := by
  have heq : pivotMatrix2284 = (fun u v => node2284 (pivotPermutation2284 u) v) := by apply Matrix.ext; unfold pivotMatrix2284 node2284 pivotPermutation2284; decide +kernel
  have hmoment : injectiveMoment H node2284 = injectiveMoment H pivotMatrix2284 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2284 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2284 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2284 (0 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2284 (0 : Fin 4) = raw4610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2284 raw4610; decide +kernel
    rw [heq]
    exact (canonical4610 hH).trans (sound1308 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2284 (1 : Fin 4)) =
      Sparse.eval value1365 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2284 (1 : Fin 4) = raw4833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2284 raw4833; decide +kernel
    rw [heq]
    exact (canonical4833 hH).trans (sound1365 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2284 (2 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2284 (2 : Fin 4) = raw4837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2284 raw4837; decide +kernel
    rw [heq]
    exact (canonical4837 hH).trans (sound487 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2284 (3 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2284 (3 : Fin 4) = raw4838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2284 raw4838; decide +kernel
    rw [heq]
    exact (canonical4838 hH).trans (sound1309 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2284 + (injectiveMoment H (mergeFirst pivotMatrix2284 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2284 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2284 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2284 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2284, value1308, value1309, value1365, value487, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2285 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2285 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem sound2285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2285 = Sparse.eval value2285 (momentVector H) := by
  have heq : pivotMatrix2285 = (fun u v => node2285 (pivotPermutation2285 u) v) := by apply Matrix.ext; unfold pivotMatrix2285 node2285 pivotPermutation2285; decide +kernel
  have hmoment : injectiveMoment H node2285 = injectiveMoment H pivotMatrix2285 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2285 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2285 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2285 (0 : Fin 4)) =
      Sparse.eval value984 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2285 (0 : Fin 4) = raw4617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2285 raw4617; decide +kernel
    rw [heq]
    exact (canonical4617 hH).trans (sound984 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2285 (1 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2285 (1 : Fin 4) = raw4837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2285 raw4837; decide +kernel
    rw [heq]
    exact (canonical4837 hH).trans (sound487 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2285 (2 : Fin 4)) =
      Sparse.eval value1093 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2285 (2 : Fin 4) = raw4840 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2285 raw4840; decide +kernel
    rw [heq]
    exact (canonical4840 hH).trans (sound1093 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2285 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2285 (3 : Fin 4) = raw4841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2285 raw4841; decide +kernel
    rw [heq]
    exact (canonical4841 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2285 + (injectiveMoment H (mergeFirst pivotMatrix2285 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2285 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2285 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2285 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2285, value1078, value1093, value487, value984, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2286 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2286 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem sound2286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2286 = Sparse.eval value2286 (momentVector H) := by
  have heq : pivotMatrix2286 = (fun u v => node2286 (pivotPermutation2286 u) v) := by apply Matrix.ext; unfold pivotMatrix2286 node2286 pivotPermutation2286; decide +kernel
  have hmoment : injectiveMoment H node2286 = injectiveMoment H pivotMatrix2286 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2286 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2286 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2286 (0 : Fin 4)) =
      Sparse.eval value1089 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2286 (0 : Fin 4) = raw4630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2286 raw4630; decide +kernel
    rw [heq]
    exact (canonical4630 hH).trans (sound1089 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2286 (1 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2286 (1 : Fin 4) = raw4846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2286 raw4846; decide +kernel
    rw [heq]
    exact (canonical4846 hH).trans (sound1347 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2286 (2 : Fin 4)) =
      Sparse.eval value1343 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2286 (2 : Fin 4) = raw4848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2286 raw4848; decide +kernel
    rw [heq]
    exact (canonical4848 hH).trans (sound1343 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2286 (3 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2286 (3 : Fin 4) = raw4849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2286 raw4849; decide +kernel
    rw [heq]
    exact (canonical4849 hH).trans (sound693 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2286 + (injectiveMoment H (mergeFirst pivotMatrix2286 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2286 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2286 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2286 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2286, value1089, value1343, value1347, value693, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2287 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2287 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem sound2287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2287 = Sparse.eval value2287 (momentVector H) := by
  have heq : pivotMatrix2287 = (fun u v => node2287 (pivotPermutation2287 u) v) := by apply Matrix.ext; unfold pivotMatrix2287 node2287 pivotPermutation2287; decide +kernel
  have hmoment : injectiveMoment H node2287 = injectiveMoment H pivotMatrix2287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2287 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2287 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2287 (0 : Fin 4)) =
      Sparse.eval value687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2287 (0 : Fin 4) = raw4631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2287 raw4631; decide +kernel
    rw [heq]
    exact (canonical4631 hH).trans (sound687 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2287 (1 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2287 (1 : Fin 4) = raw4847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2287 raw4847; decide +kernel
    rw [heq]
    exact (canonical4847 hH).trans (sound477 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2287 (2 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2287 (2 : Fin 4) = raw4849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2287 raw4849; decide +kernel
    rw [heq]
    exact (canonical4849 hH).trans (sound693 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2287 (3 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2287 (3 : Fin 4) = raw4850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2287 raw4850; decide +kernel
    rw [heq]
    exact (canonical4850 hH).trans (sound693 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2287 + (injectiveMoment H (mergeFirst pivotMatrix2287 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2287 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2287 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2287 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2287, value477, value687, value693, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2288 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2288 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

theorem sound2288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2288 = Sparse.eval value2288 (momentVector H) := by
  have heq : pivotMatrix2288 = (fun u v => node2288 (pivotPermutation2288 u) v) := by apply Matrix.ext; unfold pivotMatrix2288 node2288 pivotPermutation2288; decide +kernel
  have hmoment : injectiveMoment H node2288 = injectiveMoment H pivotMatrix2288 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2288 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2288 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2288 (0 : Fin 4)) =
      Sparse.eval value790 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2288 (0 : Fin 4) = raw5031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2288 raw5031; decide +kernel
    rw [heq]
    exact (canonical5031 hH).trans (sound790 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2288 (1 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2288 (1 : Fin 4) = raw4817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2288 raw4817; decide +kernel
    rw [heq]
    exact (canonical4817 hH).trans (sound405 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2288 (2 : Fin 4)) =
      Sparse.eval value1196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2288 (2 : Fin 4) = raw4800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2288 raw4800; decide +kernel
    rw [heq]
    exact (canonical4800 hH).trans (sound1196 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2288 (3 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2288 (3 : Fin 4) = raw4799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2288 raw4799; decide +kernel
    rw [heq]
    exact (canonical4799 hH).trans (sound828 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2288 + (injectiveMoment H (mergeFirst pivotMatrix2288 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2288 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2288 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2288 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2288, value1196, value405, value790, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2289 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2289 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

theorem sound2289 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2289 = Sparse.eval value2289 (momentVector H) := by
  have heq : pivotMatrix2289 = (fun u v => node2289 (pivotPermutation2289 u) v) := by apply Matrix.ext; unfold pivotMatrix2289 node2289 pivotPermutation2289; decide +kernel
  have hmoment : injectiveMoment H node2289 = injectiveMoment H pivotMatrix2289 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2289 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2289 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2289 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2289 (0 : Fin 4) = raw5035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2289 raw5035; decide +kernel
    rw [heq]
    exact (canonical5035 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2289 (1 : Fin 4)) =
      Sparse.eval value1017 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2289 (1 : Fin 4) = raw4824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2289 raw4824; decide +kernel
    rw [heq]
    exact (canonical4824 hH).trans (sound1017 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2289 (2 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2289 (2 : Fin 4) = raw4816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2289 raw4816; decide +kernel
    rw [heq]
    exact (canonical4816 hH).trans (sound831 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2289 (3 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2289 (3 : Fin 4) = raw4814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2289 raw4814; decide +kernel
    rw [heq]
    exact (canonical4814 hH).trans (sound1010 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2289 + (injectiveMoment H (mergeFirst pivotMatrix2289 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2289 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2289 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2289 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2289, value1010, value1017, value1059, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2290 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2290 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

theorem sound2290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2290 = Sparse.eval value2290 (momentVector H) := by
  have heq : pivotMatrix2290 = (fun u v => node2290 (pivotPermutation2290 u) v) := by apply Matrix.ext; unfold pivotMatrix2290 node2290 pivotPermutation2290; decide +kernel
  have hmoment : injectiveMoment H node2290 = injectiveMoment H pivotMatrix2290 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2290 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2290 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2290 (0 : Fin 4)) =
      Sparse.eval value794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2290 (0 : Fin 4) = raw5036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2290 raw5036; decide +kernel
    rw [heq]
    exact (canonical5036 hH).trans (sound794 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2290 (1 : Fin 4)) =
      Sparse.eval value1025 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2290 (1 : Fin 4) = raw4825 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2290 raw4825; decide +kernel
    rw [heq]
    exact (canonical4825 hH).trans (sound1025 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2290 (2 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2290 (2 : Fin 4) = raw4817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2290 raw4817; decide +kernel
    rw [heq]
    exact (canonical4817 hH).trans (sound405 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2290 (3 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2290 (3 : Fin 4) = raw4816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2290 raw4816; decide +kernel
    rw [heq]
    exact (canonical4816 hH).trans (sound831 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2290 + (injectiveMoment H (mergeFirst pivotMatrix2290 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2290 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2290 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2290 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2290, value1025, value405, value794, value831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2291 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2291 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 0, 1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

theorem sound2291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2291 = Sparse.eval value2291 (momentVector H) := by
  have heq : pivotMatrix2291 = (fun u v => node2291 (pivotPermutation2291 u) v) := by apply Matrix.ext; unfold pivotMatrix2291 node2291 pivotPermutation2291; decide +kernel
  have hmoment : injectiveMoment H node2291 = injectiveMoment H pivotMatrix2291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2291 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2291 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2291 (0 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2291 (0 : Fin 4) = raw5040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2291 raw5040; decide +kernel
    rw [heq]
    exact (canonical5040 hH).trans (sound1111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2291 (1 : Fin 4)) =
      Sparse.eval value1111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2291 (1 : Fin 4) = raw4842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2291 raw4842; decide +kernel
    rw [heq]
    exact (canonical4842 hH).trans (sound1111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2291 (2 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2291 (2 : Fin 4) = raw4841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2291 raw4841; decide +kernel
    rw [heq]
    exact (canonical4841 hH).trans (sound1078 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2291 (3 : Fin 4)) =
      Sparse.eval value1093 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2291 (3 : Fin 4) = raw4840 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2291 raw4840; decide +kernel
    rw [heq]
    exact (canonical4840 hH).trans (sound1093 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2291 + (injectiveMoment H (mergeFirst pivotMatrix2291 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2291 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2291 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2291 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2291, value1078, value1093, value1111, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2292 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2292 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 1, -1]]

theorem sound2292 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2292 = Sparse.eval value2292 (momentVector H) := by
  have heq : pivotMatrix2292 = (fun u v => node2292 (pivotPermutation2292 u) v) := by apply Matrix.ext; unfold pivotMatrix2292 node2292 pivotPermutation2292; decide +kernel
  have hmoment : injectiveMoment H node2292 = injectiveMoment H pivotMatrix2292 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2292 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2292 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2292 (0 : Fin 4)) =
      Sparse.eval value503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2292 (0 : Fin 4) = raw5370 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2292 raw5370; decide +kernel
    rw [heq]
    exact (canonical5370 hH).trans (sound503 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2292 (1 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2292 (1 : Fin 4) = raw4845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2292 raw4845; decide +kernel
    rw [heq]
    exact (canonical4845 hH).trans (sound513 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2292 (2 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2292 (2 : Fin 4) = raw4821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2292 raw4821; decide +kernel
    rw [heq]
    exact (canonical4821 hH).trans (sound1347 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2292 (3 : Fin 4)) =
      Sparse.eval value840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2292 (3 : Fin 4) = raw4820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2292 raw4820; decide +kernel
    rw [heq]
    exact (canonical4820 hH).trans (sound840 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2292 + (injectiveMoment H (mergeFirst pivotMatrix2292 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2292 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2292 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2292 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2292, value1347, value503, value513, value840, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2293 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2293 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem sound2293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2293 = Sparse.eval value2293 (momentVector H) := by
  have heq : pivotMatrix2293 = (fun u v => node2293 (pivotPermutation2293 u) v) := by apply Matrix.ext; unfold pivotMatrix2293 node2293 pivotPermutation2293; decide +kernel
  have hmoment : injectiveMoment H node2293 = injectiveMoment H pivotMatrix2293 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2293 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2293 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2293 (0 : Fin 4)) =
      Sparse.eval value989 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2293 (0 : Fin 4) = raw5373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2293 raw5373; decide +kernel
    rw [heq]
    exact (canonical5373 hH).trans (sound989 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2293 (1 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2293 (1 : Fin 4) = raw4846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2293 raw4846; decide +kernel
    rw [heq]
    exact (canonical4846 hH).trans (sound1347 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2293 (2 : Fin 4)) =
      Sparse.eval value1355 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2293 (2 : Fin 4) = raw4829 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2293 raw4829; decide +kernel
    rw [heq]
    exact (canonical4829 hH).trans (sound1355 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2293 (3 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2293 (3 : Fin 4) = raw4826 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2293 raw4826; decide +kernel
    rw [heq]
    exact (canonical4826 hH).trans (sound1231 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2293 + (injectiveMoment H (mergeFirst pivotMatrix2293 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2293 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2293 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2293 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2293, value1231, value1347, value1355, value989, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2294 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem sound2294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2294 = Sparse.eval value2294 (momentVector H) := by
  have heq : pivotMatrix2294 = (fun u v => node2294 (pivotPermutation2294 u) v) := by apply Matrix.ext; unfold pivotMatrix2294 node2294 pivotPermutation2294; decide +kernel
  have hmoment : injectiveMoment H node2294 = injectiveMoment H pivotMatrix2294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2294 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2294 (0 : Fin 5)) =
      Sparse.eval value322 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2294 (0 : Fin 5) = raw3904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2294 raw3904; decide +kernel
    rw [heq]
    exact (canonical3904 hH).trans (sound322 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2294 (1 : Fin 5)) =
      Sparse.eval value694 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2294 (1 : Fin 5) = raw4862 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2294 raw4862; decide +kernel
    rw [heq]
    exact (canonical4862 hH).trans (sound694 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2294 (2 : Fin 5)) =
      Sparse.eval value695 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2294 (2 : Fin 5) = raw4873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2294 raw4873; decide +kernel
    rw [heq]
    exact (canonical4873 hH).trans (sound695 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2294 (3 : Fin 5)) =
      Sparse.eval value695 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2294 (3 : Fin 5) = raw4875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2294 raw4875; decide +kernel
    rw [heq]
    exact (canonical4875 hH).trans (sound695 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2294 (4 : Fin 5)) =
      Sparse.eval value374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2294 (4 : Fin 5) = raw4876 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2294 raw4876; decide +kernel
    rw [heq]
    exact (canonical4876 hH).trans (sound374 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2294 + (injectiveMoment H (mergeFirst pivotMatrix2294 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2294 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2294 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2294 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2294 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2294, value322, value374, value694, value695, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2295 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2295 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem sound2295 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2295 = Sparse.eval value2295 (momentVector H) := by
  have heq : pivotMatrix2295 = (fun u v => node2295 (pivotPermutation2295 u) v) := by apply Matrix.ext; unfold pivotMatrix2295 node2295 pivotPermutation2295; decide +kernel
  have hmoment : injectiveMoment H node2295 = injectiveMoment H pivotMatrix2295 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2295 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2295 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2295 (0 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2295 (0 : Fin 5) = raw5377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2295 raw5377; decide +kernel
    rw [heq]
    exact (canonical5377 hH).trans (sound705 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2295 (1 : Fin 5)) =
      Sparse.eval value1135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2295 (1 : Fin 5) = raw4885 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2295 raw4885; decide +kernel
    rw [heq]
    exact (canonical4885 hH).trans (sound1135 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2295 (2 : Fin 5)) =
      Sparse.eval value626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2295 (2 : Fin 5) = raw4871 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2295 raw4871; decide +kernel
    rw [heq]
    exact (canonical4871 hH).trans (sound626 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2295 (3 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2295 (3 : Fin 5) = raw4869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2295 raw4869; decide +kernel
    rw [heq]
    exact (canonical4869 hH).trans (sound1141 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2295 (4 : Fin 5)) =
      Sparse.eval value1142 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2295 (4 : Fin 5) = raw4868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2295 raw4868; decide +kernel
    rw [heq]
    exact (canonical4868 hH).trans (sound1142 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2295 + (injectiveMoment H (mergeFirst pivotMatrix2295 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2295 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2295 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2295 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2295 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2295, value1135, value1141, value1142, value626, value705, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2296 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2296 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2296 = Sparse.eval value2296 (momentVector H) := by
  have heq : pivotMatrix2296 = (fun u v => node2296 (pivotPermutation2296 u) v) := by apply Matrix.ext; unfold pivotMatrix2296 node2296 pivotPermutation2296; decide +kernel
  have hmoment : injectiveMoment H node2296 = injectiveMoment H pivotMatrix2296 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2296 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2296 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2296 (0 : Fin 5)) =
      Sparse.eval value662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2296 (0 : Fin 5) = raw5378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2296 raw5378; decide +kernel
    rw [heq]
    exact (canonical5378 hH).trans (sound662 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2296 (1 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2296 (1 : Fin 5) = raw4913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2296 raw4913; decide +kernel
    rw [heq]
    exact (canonical4913 hH).trans (sound705 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2296 (2 : Fin 5)) =
      Sparse.eval value698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2296 (2 : Fin 5) = raw4899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2296 raw4899; decide +kernel
    rw [heq]
    exact (canonical4899 hH).trans (sound698 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2296 (3 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2296 (3 : Fin 5) = raw4897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2296 raw4897; decide +kernel
    rw [heq]
    exact (canonical4897 hH).trans (sound697 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2296 (4 : Fin 5)) =
      Sparse.eval value696 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2296 (4 : Fin 5) = raw4896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2296 raw4896; decide +kernel
    rw [heq]
    exact (canonical4896 hH).trans (sound696 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2296 + (injectiveMoment H (mergeFirst pivotMatrix2296 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2296 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2296 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2296 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2296 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2296, value662, value696, value697, value698, value705, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2297 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2297 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2297 = Sparse.eval value2297 (momentVector H) := by
  have heq : pivotMatrix2297 = (fun u v => node2297 (pivotPermutation2297 u) v) := by apply Matrix.ext; unfold pivotMatrix2297 node2297 pivotPermutation2297; decide +kernel
  have hmoment : injectiveMoment H node2297 = injectiveMoment H pivotMatrix2297 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2297 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2297 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2297 (0 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2297 (0 : Fin 5) = raw5379 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2297 raw5379; decide +kernel
    rw [heq]
    exact (canonical5379 hH).trans (sound663 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2297 (1 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2297 (1 : Fin 5) = raw4914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2297 raw4914; decide +kernel
    rw [heq]
    exact (canonical4914 hH).trans (sound667 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2297 (2 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2297 (2 : Fin 5) = raw4900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2297 raw4900; decide +kernel
    rw [heq]
    exact (canonical4900 hH).trans (sound699 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2297 (3 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2297 (3 : Fin 5) = raw4898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2297 raw4898; decide +kernel
    rw [heq]
    exact (canonical4898 hH).trans (sound697 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2297 (4 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2297 (4 : Fin 5) = raw4897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2297 raw4897; decide +kernel
    rw [heq]
    exact (canonical4897 hH).trans (sound697 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2297 + (injectiveMoment H (mergeFirst pivotMatrix2297 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2297 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2297 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2297 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2297 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2297, value663, value667, value697, value699, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2298 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2298 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2298 = Sparse.eval value2298 (momentVector H) := by
  have heq : pivotMatrix2298 = (fun u v => node2298 (pivotPermutation2298 u) v) := by apply Matrix.ext; unfold pivotMatrix2298 node2298 pivotPermutation2298; decide +kernel
  have hmoment : injectiveMoment H node2298 = injectiveMoment H pivotMatrix2298 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2298 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2298 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2298 (0 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2298 (0 : Fin 5) = raw5380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2298 raw5380; decide +kernel
    rw [heq]
    exact (canonical5380 hH).trans (sound648 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2298 (1 : Fin 5)) =
      Sparse.eval value706 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2298 (1 : Fin 5) = raw4916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2298 raw4916; decide +kernel
    rw [heq]
    exact (canonical4916 hH).trans (sound706 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2298 (2 : Fin 5)) =
      Sparse.eval value700 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2298 (2 : Fin 5) = raw4902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2298 raw4902; decide +kernel
    rw [heq]
    exact (canonical4902 hH).trans (sound700 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2298 (3 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2298 (3 : Fin 5) = raw4900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2298 raw4900; decide +kernel
    rw [heq]
    exact (canonical4900 hH).trans (sound699 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2298 (4 : Fin 5)) =
      Sparse.eval value698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2298 (4 : Fin 5) = raw4899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2298 raw4899; decide +kernel
    rw [heq]
    exact (canonical4899 hH).trans (sound698 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2298 + (injectiveMoment H (mergeFirst pivotMatrix2298 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2298 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2298 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2298 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2298 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2298, value648, value698, value699, value700, value706, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2299 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2299 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound2299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2299 = Sparse.eval value2299 (momentVector H) := by
  have heq : pivotMatrix2299 = (fun u v => node2299 (pivotPermutation2299 u) v) := by apply Matrix.ext; unfold pivotMatrix2299 node2299 pivotPermutation2299; decide +kernel
  have hmoment : injectiveMoment H node2299 = injectiveMoment H pivotMatrix2299 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2299 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2299 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2299 (0 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2299 (0 : Fin 5) = raw4027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2299 raw4027; decide +kernel
    rw [heq]
    exact (canonical4027 hH).trans (sound646 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2299 (1 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2299 (1 : Fin 5) = raw4897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2299 raw4897; decide +kernel
    rw [heq]
    exact (canonical4897 hH).trans (sound697 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2299 (2 : Fin 5)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2299 (2 : Fin 5) = raw4911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2299 raw4911; decide +kernel
    rw [heq]
    exact (canonical4911 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2299 (3 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2299 (3 : Fin 5) = raw4913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2299 raw4913; decide +kernel
    rw [heq]
    exact (canonical4913 hH).trans (sound705 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2299 (4 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2299 (4 : Fin 5) = raw4914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2299 raw4914; decide +kernel
    rw [heq]
    exact (canonical4914 hH).trans (sound667 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2299 + (injectiveMoment H (mergeFirst pivotMatrix2299 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2299 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2299 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2299 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2299 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2299, value210, value646, value667, value697, value705, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2300 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2300 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2300 = Sparse.eval value2300 (momentVector H) := by
  have heq : pivotMatrix2300 = (fun u v => node2300 (pivotPermutation2300 u) v) := by apply Matrix.ext; unfold pivotMatrix2300 node2300 pivotPermutation2300; decide +kernel
  have hmoment : injectiveMoment H node2300 = injectiveMoment H pivotMatrix2300 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2300 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2300 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2300 (0 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2300 (0 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2300 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2300 (1 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2300 (1 : Fin 5) = raw4900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2300 raw4900; decide +kernel
    rw [heq]
    exact (canonical4900 hH).trans (sound699 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2300 (2 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2300 (2 : Fin 5) = raw4914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2300 raw4914; decide +kernel
    rw [heq]
    exact (canonical4914 hH).trans (sound667 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2300 (3 : Fin 5)) =
      Sparse.eval value706 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2300 (3 : Fin 5) = raw4916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2300 raw4916; decide +kernel
    rw [heq]
    exact (canonical4916 hH).trans (sound706 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2300 (4 : Fin 5)) =
      Sparse.eval value706 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2300 (4 : Fin 5) = raw4917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2300 raw4917; decide +kernel
    rw [heq]
    exact (canonical4917 hH).trans (sound706 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2300 + (injectiveMoment H (mergeFirst pivotMatrix2300 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2300 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2300 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2300 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2300 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2300, value641, value667, value699, value706, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2301 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2301 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2301 = Sparse.eval value2301 (momentVector H) := by
  have heq : pivotMatrix2301 = (fun u v => node2301 (pivotPermutation2301 u) v) := by apply Matrix.ext; unfold pivotMatrix2301 node2301 pivotPermutation2301; decide +kernel
  have hmoment : injectiveMoment H node2301 = injectiveMoment H pivotMatrix2301 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2301 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2301 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2301 (0 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2301 (0 : Fin 5) = raw5383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2301 raw5383; decide +kernel
    rw [heq]
    exact (canonical5383 hH).trans (sound661 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2301 (1 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2301 (1 : Fin 5) = raw4941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2301 raw4941; decide +kernel
    rw [heq]
    exact (canonical4941 hH).trans (sound711 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2301 (2 : Fin 5)) =
      Sparse.eval value706 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2301 (2 : Fin 5) = raw4916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2301 raw4916; decide +kernel
    rw [heq]
    exact (canonical4916 hH).trans (sound706 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2301 (3 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2301 (3 : Fin 5) = raw4914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2301 raw4914; decide +kernel
    rw [heq]
    exact (canonical4914 hH).trans (sound667 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2301 (4 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2301 (4 : Fin 5) = raw4913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2301 raw4913; decide +kernel
    rw [heq]
    exact (canonical4913 hH).trans (sound705 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2301 + (injectiveMoment H (mergeFirst pivotMatrix2301 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2301 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2301 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2301 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2301 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2301, value661, value667, value705, value706, value711, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2302 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2302 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem sound2302 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2302 = Sparse.eval value2302 (momentVector H) := by
  have heq : pivotMatrix2302 = (fun u v => node2302 (pivotPermutation2302 u) v) := by apply Matrix.ext; unfold pivotMatrix2302 node2302 pivotPermutation2302; decide +kernel
  have hmoment : injectiveMoment H node2302 = injectiveMoment H pivotMatrix2302 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2302 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2302 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2302 (0 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2302 (0 : Fin 5) = raw4058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2302 raw4058; decide +kernel
    rw [heq]
    exact (canonical4058 hH).trans (sound653 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2302 (1 : Fin 5)) =
      Sparse.eval value701 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2302 (1 : Fin 5) = raw4909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2302 raw4909; decide +kernel
    rw [heq]
    exact (canonical4909 hH).trans (sound701 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2302 (2 : Fin 5)) =
      Sparse.eval value701 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2302 (2 : Fin 5) = raw4926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2302 raw4926; decide +kernel
    rw [heq]
    exact (canonical4926 hH).trans (sound701 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2302 (3 : Fin 5)) =
      Sparse.eval value707 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2302 (3 : Fin 5) = raw4931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2302 raw4931; decide +kernel
    rw [heq]
    exact (canonical4931 hH).trans (sound707 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2302 (4 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2302 (4 : Fin 5) = raw4932 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2302 raw4932; decide +kernel
    rw [heq]
    exact (canonical4932 hH).trans (sound708 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2302 + (injectiveMoment H (mergeFirst pivotMatrix2302 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2302 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2302 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2302 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2302 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2302, value653, value701, value707, value708, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2303 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

theorem sound2303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2303 = Sparse.eval value2303 (momentVector H) := by
  have heq : pivotMatrix2303 = (fun u v => node2303 (pivotPermutation2303 u) v) := by apply Matrix.ext; unfold pivotMatrix2303 node2303 pivotPermutation2303; decide +kernel
  have hmoment : injectiveMoment H node2303 = injectiveMoment H pivotMatrix2303 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2303 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2303 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2303 (0 : Fin 5)) =
      Sparse.eval value562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2303 (0 : Fin 5) = raw4059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2303 raw4059; decide +kernel
    rw [heq]
    exact (canonical4059 hH).trans (sound562 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2303 (1 : Fin 5)) =
      Sparse.eval value702 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2303 (1 : Fin 5) = raw4910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2303 raw4910; decide +kernel
    rw [heq]
    exact (canonical4910 hH).trans (sound702 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2303 (2 : Fin 5)) =
      Sparse.eval value702 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2303 (2 : Fin 5) = raw4927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2303 raw4927; decide +kernel
    rw [heq]
    exact (canonical4927 hH).trans (sound702 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2303 (3 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2303 (3 : Fin 5) = raw4932 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2303 raw4932; decide +kernel
    rw [heq]
    exact (canonical4932 hH).trans (sound708 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2303 (4 : Fin 5)) =
      Sparse.eval value709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2303 (4 : Fin 5) = raw4933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2303 raw4933; decide +kernel
    rw [heq]
    exact (canonical4933 hH).trans (sound709 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2303 + (injectiveMoment H (mergeFirst pivotMatrix2303 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2303 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2303 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2303 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2303 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2303, value562, value702, value708, value709, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
