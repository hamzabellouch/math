import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2368 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2368 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem sound2368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2368 = Sparse.eval value2368 (momentVector H) := by
  have heq : pivotMatrix2368 = (fun u v => node2368 (pivotPermutation2368 u) v) := by apply Matrix.ext; unfold pivotMatrix2368 node2368 pivotPermutation2368; decide +kernel
  have hmoment : injectiveMoment H node2368 = injectiveMoment H pivotMatrix2368 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2368 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2368 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2368 (0 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2368 (0 : Fin 4) = raw7969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2368 raw7969; decide +kernel
    rw [heq]
    exact (canonical7969 hH).trans (sound1348 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2368 (1 : Fin 4)) =
      Sparse.eval value471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2368 (1 : Fin 4) = raw5445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2368 raw5445; decide +kernel
    rw [heq]
    exact (canonical5445 hH).trans (sound471 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2368 (2 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2368 (2 : Fin 4) = raw5400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2368 raw5400; decide +kernel
    rw [heq]
    exact (canonical5400 hH).trans (sound688 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2368 (3 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2368 (3 : Fin 4) = raw5395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2368 raw5395; decide +kernel
    rw [heq]
    exact (canonical5395 hH).trans (sound576 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2368 + (injectiveMoment H (mergeFirst pivotMatrix2368 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2368 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2368 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2368 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2368, value1348, value471, value576, value688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2369 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2369 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound2369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2369 = Sparse.eval value2369 (momentVector H) := by
  have heq : pivotMatrix2369 = (fun u v => node2369 (pivotPermutation2369 u) v) := by apply Matrix.ext; unfold pivotMatrix2369 node2369 pivotPermutation2369; decide +kernel
  have hmoment : injectiveMoment H node2369 = injectiveMoment H pivotMatrix2369 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2369 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2369 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2369 (0 : Fin 4)) =
      Sparse.eval value947 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2369 (0 : Fin 4) = raw5311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2369 raw5311; decide +kernel
    rw [heq]
    exact (canonical5311 hH).trans (sound947 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2369 (1 : Fin 4)) =
      Sparse.eval value1226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2369 (1 : Fin 4) = raw5406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2369 raw5406; decide +kernel
    rw [heq]
    exact (canonical5406 hH).trans (sound1226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2369 (2 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2369 (2 : Fin 4) = raw5408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2369 raw5408; decide +kernel
    rw [heq]
    exact (canonical5408 hH).trans (sound1010 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2369 (3 : Fin 4)) =
      Sparse.eval value475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2369 (3 : Fin 4) = raw5409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2369 raw5409; decide +kernel
    rw [heq]
    exact (canonical5409 hH).trans (sound475 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2369 + (injectiveMoment H (mergeFirst pivotMatrix2369 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2369 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2369 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2369 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2369, value1010, value1226, value475, value947, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2370 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2370 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound2370 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2370 = Sparse.eval value2370 (momentVector H) := by
  have heq : pivotMatrix2370 = (fun u v => node2370 (pivotPermutation2370 u) v) := by apply Matrix.ext; unfold pivotMatrix2370 node2370 pivotPermutation2370; decide +kernel
  have hmoment : injectiveMoment H node2370 = injectiveMoment H pivotMatrix2370 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2370 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2370 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2370 (0 : Fin 4)) =
      Sparse.eval value989 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2370 (0 : Fin 4) = raw5451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2370 raw5451; decide +kernel
    rw [heq]
    exact (canonical5451 hH).trans (sound989 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2370 (1 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2370 (1 : Fin 4) = raw5425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2370 raw5425; decide +kernel
    rw [heq]
    exact (canonical5425 hH).trans (sound1304 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2370 (2 : Fin 4)) =
      Sparse.eval value689 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2370 (2 : Fin 4) = raw5416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2370 raw5416; decide +kernel
    rw [heq]
    exact (canonical5416 hH).trans (sound689 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2370 (3 : Fin 4)) =
      Sparse.eval value1375 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2370 (3 : Fin 4) = raw5415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2370 raw5415; decide +kernel
    rw [heq]
    exact (canonical5415 hH).trans (sound1375 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2370 + (injectiveMoment H (mergeFirst pivotMatrix2370 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2370 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2370 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2370 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2370, value1304, value1375, value689, value989, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2371 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2371 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound2371 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2371 = Sparse.eval value2371 (momentVector H) := by
  have heq : pivotMatrix2371 = (fun u v => node2371 (pivotPermutation2371 u) v) := by apply Matrix.ext; unfold pivotMatrix2371 node2371 pivotPermutation2371; decide +kernel
  have hmoment : injectiveMoment H node2371 = injectiveMoment H pivotMatrix2371 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2371 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2371 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2371 (0 : Fin 4)) =
      Sparse.eval value1303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2371 (0 : Fin 4) = raw5330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2371 raw5330; decide +kernel
    rw [heq]
    exact (canonical5330 hH).trans (sound1303 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2371 (1 : Fin 4)) =
      Sparse.eval value1375 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2371 (1 : Fin 4) = raw5415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2371 raw5415; decide +kernel
    rw [heq]
    exact (canonical5415 hH).trans (sound1375 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2371 (2 : Fin 4)) =
      Sparse.eval value471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2371 (2 : Fin 4) = raw5424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2371 raw5424; decide +kernel
    rw [heq]
    exact (canonical5424 hH).trans (sound471 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2371 (3 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2371 (3 : Fin 4) = raw5425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2371 raw5425; decide +kernel
    rw [heq]
    exact (canonical5425 hH).trans (sound1304 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2371 + (injectiveMoment H (mergeFirst pivotMatrix2371 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2371 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2371 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2371 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2371, value1303, value1304, value1375, value471, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2372 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2372 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem sound2372 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2372 = Sparse.eval value2372 (momentVector H) := by
  have heq : pivotMatrix2372 = (fun u v => node2372 (pivotPermutation2372 u) v) := by apply Matrix.ext; unfold pivotMatrix2372 node2372 pivotPermutation2372; decide +kernel
  have hmoment : injectiveMoment H node2372 = injectiveMoment H pivotMatrix2372 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2372 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2372 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2372 (0 : Fin 4)) =
      Sparse.eval value503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2372 (0 : Fin 4) = raw5452 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2372 raw5452; decide +kernel
    rw [heq]
    exact (canonical5452 hH).trans (sound503 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2372 (1 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2372 (1 : Fin 4) = raw5437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2372 raw5437; decide +kernel
    rw [heq]
    exact (canonical5437 hH).trans (sound1005 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2372 (2 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2372 (2 : Fin 4) = raw5425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2372 raw5425; decide +kernel
    rw [heq]
    exact (canonical5425 hH).trans (sound1304 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2372 (3 : Fin 4)) =
      Sparse.eval value471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2372 (3 : Fin 4) = raw5424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2372 raw5424; decide +kernel
    rw [heq]
    exact (canonical5424 hH).trans (sound471 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2372 + (injectiveMoment H (mergeFirst pivotMatrix2372 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2372 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2372 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2372 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2372, value1005, value1304, value471, value503, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2373 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2373 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem sound2373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2373 = Sparse.eval value2373 (momentVector H) := by
  have heq : pivotMatrix2373 = (fun u v => node2373 (pivotPermutation2373 u) v) := by apply Matrix.ext; unfold pivotMatrix2373 node2373 pivotPermutation2373; decide +kernel
  have hmoment : injectiveMoment H node2373 = injectiveMoment H pivotMatrix2373 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2373 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2373 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2373 (0 : Fin 4)) =
      Sparse.eval value941 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2373 (0 : Fin 4) = raw5349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2373 raw5349; decide +kernel
    rw [heq]
    exact (canonical5349 hH).trans (sound941 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2373 (1 : Fin 4)) =
      Sparse.eval value471 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2373 (1 : Fin 4) = raw5424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2373 raw5424; decide +kernel
    rw [heq]
    exact (canonical5424 hH).trans (sound471 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2373 (2 : Fin 4)) =
      Sparse.eval value1188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2373 (2 : Fin 4) = raw5436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2373 raw5436; decide +kernel
    rw [heq]
    exact (canonical5436 hH).trans (sound1188 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2373 (3 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2373 (3 : Fin 4) = raw5437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2373 raw5437; decide +kernel
    rw [heq]
    exact (canonical5437 hH).trans (sound1005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2373 + (injectiveMoment H (mergeFirst pivotMatrix2373 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2373 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2373 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2373 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2373, value1005, value1188, value471, value941, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2374 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2374 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, 0, 0], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

theorem sound2374 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2374 = Sparse.eval value2374 (momentVector H) := by
  have heq : pivotMatrix2374 = (fun u v => node2374 (pivotPermutation2374 u) v) := by apply Matrix.ext; unfold pivotMatrix2374 node2374 pivotPermutation2374; decide +kernel
  have hmoment : injectiveMoment H node2374 = injectiveMoment H pivotMatrix2374 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2374 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2374 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2374 (0 : Fin 4)) =
      Sparse.eval value822 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2374 (0 : Fin 4) = raw5367 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2374 raw5367; decide +kernel
    rw [heq]
    exact (canonical5367 hH).trans (sound822 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2374 (1 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2374 (1 : Fin 4) = raw5438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2374 raw5438; decide +kernel
    rw [heq]
    exact (canonical5438 hH).trans (sound224 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2374 (2 : Fin 4)) =
      Sparse.eval value1188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2374 (2 : Fin 4) = raw5439 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2374 raw5439; decide +kernel
    rw [heq]
    exact (canonical5439 hH).trans (sound1188 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2374 (3 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2374 (3 : Fin 4) = raw5440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2374 raw5440; decide +kernel
    rw [heq]
    exact (canonical5440 hH).trans (sound1005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2374 + (injectiveMoment H (mergeFirst pivotMatrix2374 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2374 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2374 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2374 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2374, value1005, value1188, value224, value822, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2375 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound2375 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2375 = Sparse.eval value2375 (momentVector H) := by
  have heq : pivotMatrix2375 = (fun u v => node2375 (pivotPermutation2375 u) v) := by apply Matrix.ext; unfold pivotMatrix2375 node2375 pivotPermutation2375; decide +kernel
  have hmoment : injectiveMoment H node2375 = injectiveMoment H pivotMatrix2375 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2375 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2375 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2375 (0 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2375 (0 : Fin 5) = raw934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2375 raw934; decide +kernel
    rw [heq]
    exact (canonical934 hH).trans (sound387 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2375 (1 : Fin 5)) =
      Sparse.eval value721 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2375 (1 : Fin 5) = raw5461 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2375 raw5461; decide +kernel
    rw [heq]
    exact (canonical5461 hH).trans (sound721 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2375 (2 : Fin 5)) =
      Sparse.eval value721 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2375 (2 : Fin 5) = raw5471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2375 raw5471; decide +kernel
    rw [heq]
    exact (canonical5471 hH).trans (sound721 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2375 (3 : Fin 5)) =
      Sparse.eval value723 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2375 (3 : Fin 5) = raw5472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2375 raw5472; decide +kernel
    rw [heq]
    exact (canonical5472 hH).trans (sound723 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2375 (4 : Fin 5)) =
      Sparse.eval value724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2375 (4 : Fin 5) = raw5474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2375 raw5474; decide +kernel
    rw [heq]
    exact (canonical5474 hH).trans (sound724 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2375 + (injectiveMoment H (mergeFirst pivotMatrix2375 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2375 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2375 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2375 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2375 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2375, value387, value721, value723, value724, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2376 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem sound2376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2376 = Sparse.eval value2376 (momentVector H) := by
  have heq : pivotMatrix2376 = (fun u v => node2376 (pivotPermutation2376 u) v) := by apply Matrix.ext; unfold pivotMatrix2376 node2376 pivotPermutation2376; decide +kernel
  have hmoment : injectiveMoment H node2376 = injectiveMoment H pivotMatrix2376 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2376 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2376 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2376 (0 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2376 (0 : Fin 5) = raw5526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2376 raw5526; decide +kernel
    rw [heq]
    exact (canonical5526 hH).trans (sound748 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2376 (1 : Fin 5)) =
      Sparse.eval value724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2376 (1 : Fin 5) = raw5480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2376 raw5480; decide +kernel
    rw [heq]
    exact (canonical5480 hH).trans (sound724 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2376 (2 : Fin 5)) =
      Sparse.eval value724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2376 (2 : Fin 5) = raw5476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2376 raw5476; decide +kernel
    rw [heq]
    exact (canonical5476 hH).trans (sound724 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2376 (3 : Fin 5)) =
      Sparse.eval value724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2376 (3 : Fin 5) = raw5473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2376 raw5473; decide +kernel
    rw [heq]
    exact (canonical5473 hH).trans (sound724 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2376 (4 : Fin 5)) =
      Sparse.eval value723 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2376 (4 : Fin 5) = raw5472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2376 raw5472; decide +kernel
    rw [heq]
    exact (canonical5472 hH).trans (sound723 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2376 + (injectiveMoment H (mergeFirst pivotMatrix2376 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2376 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2376 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2376 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2376 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2376, value723, value724, value748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2377 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound2377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2377 = Sparse.eval value2377 (momentVector H) := by
  have heq : pivotMatrix2377 = (fun u v => node2377 (pivotPermutation2377 u) v) := by apply Matrix.ext; unfold pivotMatrix2377 node2377 pivotPermutation2377; decide +kernel
  have hmoment : injectiveMoment H node2377 = injectiveMoment H pivotMatrix2377 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2377 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2377 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2377 (0 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2377 (0 : Fin 5) = raw934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2377 raw934; decide +kernel
    rw [heq]
    exact (canonical934 hH).trans (sound387 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2377 (1 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2377 (1 : Fin 5) = raw5490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2377 raw5490; decide +kernel
    rw [heq]
    exact (canonical5490 hH).trans (sound737 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2377 (2 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2377 (2 : Fin 5) = raw5520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2377 raw5520; decide +kernel
    rw [heq]
    exact (canonical5520 hH).trans (sound737 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2377 (3 : Fin 5)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2377 (3 : Fin 5) = raw5525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2377 raw5525; decide +kernel
    rw [heq]
    exact (canonical5525 hH).trans (sound253 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2377 (4 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2377 (4 : Fin 5) = raw5529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2377 raw5529; decide +kernel
    rw [heq]
    exact (canonical5529 hH).trans (sound748 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2377 + (injectiveMoment H (mergeFirst pivotMatrix2377 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2377 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2377 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2377 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2377 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2377, value253, value387, value737, value748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2378 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2378 = Sparse.eval value2378 (momentVector H) := by
  have heq : pivotMatrix2378 = (fun u v => node2378 (pivotPermutation2378 u) v) := by apply Matrix.ext; unfold pivotMatrix2378 node2378 pivotPermutation2378; decide +kernel
  have hmoment : injectiveMoment H node2378 = injectiveMoment H pivotMatrix2378 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2378 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2378 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2378 (0 : Fin 5)) =
      Sparse.eval value389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2378 (0 : Fin 5) = raw939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2378 raw939; decide +kernel
    rw [heq]
    exact (canonical939 hH).trans (sound389 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2378 (1 : Fin 5)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2378 (1 : Fin 5) = raw5491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2378 raw5491; decide +kernel
    rw [heq]
    exact (canonical5491 hH).trans (sound739 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2378 (2 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2378 (2 : Fin 5) = raw5522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2378 raw5522; decide +kernel
    rw [heq]
    exact (canonical5522 hH).trans (sound742 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2378 (3 : Fin 5)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2378 (3 : Fin 5) = raw5531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2378 raw5531; decide +kernel
    rw [heq]
    exact (canonical5531 hH).trans (sound254 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2378 (4 : Fin 5)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2378 (4 : Fin 5) = raw5535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2378 raw5535; decide +kernel
    rw [heq]
    exact (canonical5535 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2378 + (injectiveMoment H (mergeFirst pivotMatrix2378 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2378 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2378 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2378 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2378 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2378, value254, value389, value739, value742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2379 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2379 = Sparse.eval value2379 (momentVector H) := by
  have heq : pivotMatrix2379 = (fun u v => node2379 (pivotPermutation2379 u) v) := by apply Matrix.ext; unfold pivotMatrix2379 node2379 pivotPermutation2379; decide +kernel
  have hmoment : injectiveMoment H node2379 = injectiveMoment H pivotMatrix2379 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2379 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2379 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2379 (0 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2379 (0 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2379 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2379 (1 : Fin 5)) =
      Sparse.eval value741 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2379 (1 : Fin 5) = raw5494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2379 raw5494; decide +kernel
    rw [heq]
    exact (canonical5494 hH).trans (sound741 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2379 (2 : Fin 5)) =
      Sparse.eval value741 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2379 (2 : Fin 5) = raw5521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2379 raw5521; decide +kernel
    rw [heq]
    exact (canonical5521 hH).trans (sound741 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2379 (3 : Fin 5)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2379 (3 : Fin 5) = raw5525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2379 raw5525; decide +kernel
    rw [heq]
    exact (canonical5525 hH).trans (sound253 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2379 (4 : Fin 5)) =
      Sparse.eval value749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2379 (4 : Fin 5) = raw5528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2379 raw5528; decide +kernel
    rw [heq]
    exact (canonical5528 hH).trans (sound749 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2379 + (injectiveMoment H (mergeFirst pivotMatrix2379 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2379 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2379 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2379 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2379 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2379, value253, value440, value741, value749, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2380 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2380 = Sparse.eval value2380 (momentVector H) := by
  have heq : pivotMatrix2380 = (fun u v => node2380 (pivotPermutation2380 u) v) := by apply Matrix.ext; unfold pivotMatrix2380 node2380 pivotPermutation2380; decide +kernel
  have hmoment : injectiveMoment H node2380 = injectiveMoment H pivotMatrix2380 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2380 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2380 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2380 (0 : Fin 5)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2380 (0 : Fin 5) = raw1402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2380 raw1402; decide +kernel
    rw [heq]
    exact (canonical1402 hH).trans (sound441 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2380 (1 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2380 (1 : Fin 5) = raw5495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2380 raw5495; decide +kernel
    rw [heq]
    exact (canonical5495 hH).trans (sound742 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2380 (2 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2380 (2 : Fin 5) = raw5522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2380 raw5522; decide +kernel
    rw [heq]
    exact (canonical5522 hH).trans (sound742 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2380 (3 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2380 (3 : Fin 5) = raw5526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2380 raw5526; decide +kernel
    rw [heq]
    exact (canonical5526 hH).trans (sound748 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2380 (4 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2380 (4 : Fin 5) = raw5529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2380 raw5529; decide +kernel
    rw [heq]
    exact (canonical5529 hH).trans (sound748 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2380 + (injectiveMoment H (mergeFirst pivotMatrix2380 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2380 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2380 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2380 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2380 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2380, value441, value742, value748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2381 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2381 = Sparse.eval value2381 (momentVector H) := by
  have heq : pivotMatrix2381 = (fun u v => node2381 (pivotPermutation2381 u) v) := by apply Matrix.ext; unfold pivotMatrix2381 node2381 pivotPermutation2381; decide +kernel
  have hmoment : injectiveMoment H node2381 = injectiveMoment H pivotMatrix2381 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2381 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2381 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2381 (0 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2381 (0 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2381 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2381 (1 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2381 (1 : Fin 5) = raw5496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2381 raw5496; decide +kernel
    rw [heq]
    exact (canonical5496 hH).trans (sound743 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2381 (2 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2381 (2 : Fin 5) = raw5523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2381 raw5523; decide +kernel
    rw [heq]
    exact (canonical5523 hH).trans (sound744 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2381 (3 : Fin 5)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2381 (3 : Fin 5) = raw5531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2381 raw5531; decide +kernel
    rw [heq]
    exact (canonical5531 hH).trans (sound254 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2381 (4 : Fin 5)) =
      Sparse.eval value749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2381 (4 : Fin 5) = raw5533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2381 raw5533; decide +kernel
    rw [heq]
    exact (canonical5533 hH).trans (sound749 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2381 + (injectiveMoment H (mergeFirst pivotMatrix2381 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2381 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2381 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2381 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2381 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2381, value254, value443, value743, value744, value749, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2382 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2382 = Sparse.eval value2382 (momentVector H) := by
  have heq : pivotMatrix2382 = (fun u v => node2382 (pivotPermutation2382 u) v) := by apply Matrix.ext; unfold pivotMatrix2382 node2382 pivotPermutation2382; decide +kernel
  have hmoment : injectiveMoment H node2382 = injectiveMoment H pivotMatrix2382 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2382 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2382 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2382 (0 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2382 (0 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2382 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2382 (1 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2382 (1 : Fin 5) = raw5503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2382 raw5503; decide +kernel
    rw [heq]
    exact (canonical5503 hH).trans (sound744 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2382 (2 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2382 (2 : Fin 5) = raw5496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2382 raw5496; decide +kernel
    rw [heq]
    exact (canonical5496 hH).trans (sound743 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2382 (3 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2382 (3 : Fin 5) = raw5495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2382 raw5495; decide +kernel
    rw [heq]
    exact (canonical5495 hH).trans (sound742 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2382 (4 : Fin 5)) =
      Sparse.eval value741 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2382 (4 : Fin 5) = raw5494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2382 raw5494; decide +kernel
    rw [heq]
    exact (canonical5494 hH).trans (sound741 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2382 + (injectiveMoment H (mergeFirst pivotMatrix2382 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2382 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2382 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2382 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2382 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2382, value741, value742, value743, value744, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2383 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2383 = Sparse.eval value2383 (momentVector H) := by
  have heq : pivotMatrix2383 = (fun u v => node2383 (pivotPermutation2383 u) v) := by apply Matrix.ext; unfold pivotMatrix2383 node2383 pivotPermutation2383; decide +kernel
  have hmoment : injectiveMoment H node2383 = injectiveMoment H pivotMatrix2383 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2383 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2383 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2383 (0 : Fin 5)) =
      Sparse.eval value722 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2383 (0 : Fin 5) = raw5465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2383 raw5465; decide +kernel
    rw [heq]
    exact (canonical5465 hH).trans (sound722 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2383 (1 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2383 (1 : Fin 5) = raw5495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2383 raw5495; decide +kernel
    rw [heq]
    exact (canonical5495 hH).trans (sound742 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2383 (2 : Fin 5)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2383 (2 : Fin 5) = raw5502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2383 raw5502; decide +kernel
    rw [heq]
    exact (canonical5502 hH).trans (sound248 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2383 (3 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2383 (3 : Fin 5) = raw5503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2383 raw5503; decide +kernel
    rw [heq]
    exact (canonical5503 hH).trans (sound744 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2383 (4 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2383 (4 : Fin 5) = raw5504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2383 raw5504; decide +kernel
    rw [heq]
    exact (canonical5504 hH).trans (sound744 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2383 + (injectiveMoment H (mergeFirst pivotMatrix2383 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2383 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2383 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2383 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2383 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2383, value248, value722, value742, value744, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2384 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem sound2384 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2384 = Sparse.eval value2384 (momentVector H) := by
  have heq : pivotMatrix2384 = (fun u v => node2384 (pivotPermutation2384 u) v) := by apply Matrix.ext; unfold pivotMatrix2384 node2384 pivotPermutation2384; decide +kernel
  have hmoment : injectiveMoment H node2384 = injectiveMoment H pivotMatrix2384 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2384 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2384 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2384 (0 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2384 (0 : Fin 5) = raw5959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2384 raw5959; decide +kernel
    rw [heq]
    exact (canonical5959 hH).trans (sound884 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2384 (1 : Fin 5)) =
      Sparse.eval value749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2384 (1 : Fin 5) = raw5542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2384 raw5542; decide +kernel
    rw [heq]
    exact (canonical5542 hH).trans (sound749 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2384 (2 : Fin 5)) =
      Sparse.eval value749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2384 (2 : Fin 5) = raw5532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2384 raw5532; decide +kernel
    rw [heq]
    exact (canonical5532 hH).trans (sound749 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2384 (3 : Fin 5)) =
      Sparse.eval value749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2384 (3 : Fin 5) = raw5527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2384 raw5527; decide +kernel
    rw [heq]
    exact (canonical5527 hH).trans (sound749 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2384 (4 : Fin 5)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2384 (4 : Fin 5) = raw5526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2384 raw5526; decide +kernel
    rw [heq]
    exact (canonical5526 hH).trans (sound748 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2384 + (injectiveMoment H (mergeFirst pivotMatrix2384 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2384 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2384 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2384 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2384 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2384, value748, value749, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2385 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2385 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem sound2385 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2385 = Sparse.eval value2385 (momentVector H) := by
  have heq : pivotMatrix2385 = (fun u v => node2385 (pivotPermutation2385 u) v) := by apply Matrix.ext; unfold pivotMatrix2385 node2385 pivotPermutation2385; decide +kernel
  have hmoment : injectiveMoment H node2385 = injectiveMoment H pivotMatrix2385 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2385 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2385 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2385 (0 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2385 (0 : Fin 4) = raw5596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2385 raw5596; decide +kernel
    rw [heq]
    exact (canonical5596 hH).trans (sound910 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2385 (1 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2385 (1 : Fin 4) = raw5567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2385 raw5567; decide +kernel
    rw [heq]
    exact (canonical5567 hH).trans (sound751 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2385 (2 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2385 (2 : Fin 4) = raw5563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2385 raw5563; decide +kernel
    rw [heq]
    exact (canonical5563 hH).trans (sound750 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2385 (3 : Fin 4)) =
      Sparse.eval value889 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2385 (3 : Fin 4) = raw5561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2385 raw5561; decide +kernel
    rw [heq]
    exact (canonical5561 hH).trans (sound889 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2385 + (injectiveMoment H (mergeFirst pivotMatrix2385 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2385 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2385 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2385 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2385, value750, value751, value889, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2386 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2386 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2386 = Sparse.eval value2386 (momentVector H) := by
  have heq : pivotMatrix2386 = (fun u v => node2386 (pivotPermutation2386 u) v) := by apply Matrix.ext; unfold pivotMatrix2386 node2386 pivotPermutation2386; decide +kernel
  have hmoment : injectiveMoment H node2386 = injectiveMoment H pivotMatrix2386 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2386 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2386 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2386 (0 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2386 (0 : Fin 4) = raw5601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2386 raw5601; decide +kernel
    rw [heq]
    exact (canonical5601 hH).trans (sound915 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2386 (1 : Fin 4)) =
      Sparse.eval value754 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2386 (1 : Fin 4) = raw5568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2386 raw5568; decide +kernel
    rw [heq]
    exact (canonical5568 hH).trans (sound754 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2386 (2 : Fin 4)) =
      Sparse.eval value890 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2386 (2 : Fin 4) = raw5565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2386 raw5565; decide +kernel
    rw [heq]
    exact (canonical5565 hH).trans (sound890 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2386 (3 : Fin 4)) =
      Sparse.eval value751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2386 (3 : Fin 4) = raw5564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2386 raw5564; decide +kernel
    rw [heq]
    exact (canonical5564 hH).trans (sound751 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2386 + (injectiveMoment H (mergeFirst pivotMatrix2386 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2386 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2386 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2386 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2386, value751, value754, value890, value915, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2387 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2387 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2387 = Sparse.eval value2387 (momentVector H) := by
  have heq : pivotMatrix2387 = (fun u v => node2387 (pivotPermutation2387 u) v) := by apply Matrix.ext; unfold pivotMatrix2387 node2387 pivotPermutation2387; decide +kernel
  have hmoment : injectiveMoment H node2387 = injectiveMoment H pivotMatrix2387 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2387 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2387 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2387 (0 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2387 (0 : Fin 4) = raw5626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2387 raw5626; decide +kernel
    rw [heq]
    exact (canonical5626 hH).trans (sound910 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2387 (1 : Fin 4)) =
      Sparse.eval value755 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2387 (1 : Fin 4) = raw5572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2387 raw5572; decide +kernel
    rw [heq]
    exact (canonical5572 hH).trans (sound755 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2387 (2 : Fin 4)) =
      Sparse.eval value890 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2387 (2 : Fin 4) = raw5571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2387 raw5571; decide +kernel
    rw [heq]
    exact (canonical5571 hH).trans (sound890 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2387 (3 : Fin 4)) =
      Sparse.eval value750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2387 (3 : Fin 4) = raw5570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2387 raw5570; decide +kernel
    rw [heq]
    exact (canonical5570 hH).trans (sound750 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2387 + (injectiveMoment H (mergeFirst pivotMatrix2387 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2387 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2387 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2387 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2387, value750, value755, value890, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2388 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2388 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

theorem sound2388 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2388 = Sparse.eval value2388 (momentVector H) := by
  have heq : pivotMatrix2388 = (fun u v => node2388 (pivotPermutation2388 u) v) := by apply Matrix.ext; unfold pivotMatrix2388 node2388 pivotPermutation2388; decide +kernel
  have hmoment : injectiveMoment H node2388 = injectiveMoment H pivotMatrix2388 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2388 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2388 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2388 (0 : Fin 4)) =
      Sparse.eval value888 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2388 (0 : Fin 4) = raw5558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2388 raw5558; decide +kernel
    rw [heq]
    exact (canonical5558 hH).trans (sound888 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2388 (1 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2388 (1 : Fin 4) = raw5580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2388 raw5580; decide +kernel
    rw [heq]
    exact (canonical5580 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2388 (2 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2388 (2 : Fin 4) = raw5581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2388 raw5581; decide +kernel
    rw [heq]
    exact (canonical5581 hH).trans (sound254 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2388 (3 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2388 (3 : Fin 4) = raw5587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2388 raw5587; decide +kernel
    rw [heq]
    exact (canonical5587 hH).trans (sound907 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2388 + (injectiveMoment H (mergeFirst pivotMatrix2388 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2388 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2388 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2388 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2388, value254, value888, value907, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2389 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2389 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

theorem sound2389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2389 = Sparse.eval value2389 (momentVector H) := by
  have heq : pivotMatrix2389 = (fun u v => node2389 (pivotPermutation2389 u) v) := by apply Matrix.ext; unfold pivotMatrix2389 node2389 pivotPermutation2389; decide +kernel
  have hmoment : injectiveMoment H node2389 = injectiveMoment H pivotMatrix2389 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2389 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2389 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2389 (0 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2389 (0 : Fin 4) = raw5674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2389 raw5674; decide +kernel
    rw [heq]
    exact (canonical5674 hH).trans (sound967 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2389 (1 : Fin 4)) =
      Sparse.eval value765 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2389 (1 : Fin 4) = raw5607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2389 raw5607; decide +kernel
    rw [heq]
    exact (canonical5607 hH).trans (sound765 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2389 (2 : Fin 4)) =
      Sparse.eval value765 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2389 (2 : Fin 4) = raw5591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2389 raw5591; decide +kernel
    rw [heq]
    exact (canonical5591 hH).trans (sound765 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2389 (3 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2389 (3 : Fin 4) = raw5587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2389 raw5587; decide +kernel
    rw [heq]
    exact (canonical5587 hH).trans (sound907 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2389 + (injectiveMoment H (mergeFirst pivotMatrix2389 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2389 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2389 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2389 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2389, value765, value907, value967, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2390 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2390 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem sound2390 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2390 = Sparse.eval value2390 (momentVector H) := by
  have heq : pivotMatrix2390 = (fun u v => node2390 (pivotPermutation2390 u) v) := by apply Matrix.ext; unfold pivotMatrix2390 node2390 pivotPermutation2390; decide +kernel
  have hmoment : injectiveMoment H node2390 = injectiveMoment H pivotMatrix2390 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2390 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2390 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2390 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2390 (0 : Fin 4) = raw5677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2390 raw5677; decide +kernel
    rw [heq]
    exact (canonical5677 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2390 (1 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2390 (1 : Fin 4) = raw5609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2390 raw5609; decide +kernel
    rw [heq]
    exact (canonical5609 hH).trans (sound771 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2390 (2 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2390 (2 : Fin 4) = raw5596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2390 raw5596; decide +kernel
    rw [heq]
    exact (canonical5596 hH).trans (sound910 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2390 (3 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2390 (3 : Fin 4) = raw5594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2390 raw5594; decide +kernel
    rw [heq]
    exact (canonical5594 hH).trans (sound1176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2390 + (injectiveMoment H (mergeFirst pivotMatrix2390 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2390 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2390 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2390 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2390, value1176, value1202, value771, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2391 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2391 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem sound2391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2391 = Sparse.eval value2391 (momentVector H) := by
  have heq : pivotMatrix2391 = (fun u v => node2391 (pivotPermutation2391 u) v) := by apply Matrix.ext; unfold pivotMatrix2391 node2391 pivotPermutation2391; decide +kernel
  have hmoment : injectiveMoment H node2391 = injectiveMoment H pivotMatrix2391 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2391 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2391 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2391 (0 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2391 (0 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2391 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2391 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2391 (1 : Fin 4) = raw5610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2391 raw5610; decide +kernel
    rw [heq]
    exact (canonical5610 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2391 (2 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2391 (2 : Fin 4) = raw5597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2391 raw5597; decide +kernel
    rw [heq]
    exact (canonical5597 hH).trans (sound766 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2391 (3 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2391 (3 : Fin 4) = raw5596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2391 raw5596; decide +kernel
    rw [heq]
    exact (canonical5596 hH).trans (sound910 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2391 + (injectiveMoment H (mergeFirst pivotMatrix2391 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2391 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2391 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2391 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2391, value766, value769, value910, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2392 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2392 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem sound2392 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2392 = Sparse.eval value2392 (momentVector H) := by
  have heq : pivotMatrix2392 = (fun u v => node2392 (pivotPermutation2392 u) v) := by apply Matrix.ext; unfold pivotMatrix2392 node2392 pivotPermutation2392; decide +kernel
  have hmoment : injectiveMoment H node2392 = injectiveMoment H pivotMatrix2392 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2392 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2392 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2392 (0 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2392 (0 : Fin 4) = raw5681 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2392 raw5681; decide +kernel
    rw [heq]
    exact (canonical5681 hH).trans (sound801 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2392 (1 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2392 (1 : Fin 4) = raw5611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2392 raw5611; decide +kernel
    rw [heq]
    exact (canonical5611 hH).trans (sound772 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2392 (2 : Fin 4)) =
      Sparse.eval value767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2392 (2 : Fin 4) = raw5598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2392 raw5598; decide +kernel
    rw [heq]
    exact (canonical5598 hH).trans (sound767 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2392 (3 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2392 (3 : Fin 4) = raw5597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2392 raw5597; decide +kernel
    rw [heq]
    exact (canonical5597 hH).trans (sound766 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2392 + (injectiveMoment H (mergeFirst pivotMatrix2392 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2392 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2392 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2392 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2392, value766, value767, value772, value801, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2393 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2393 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound2393 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2393 = Sparse.eval value2393 (momentVector H) := by
  have heq : pivotMatrix2393 = (fun u v => node2393 (pivotPermutation2393 u) v) := by apply Matrix.ext; unfold pivotMatrix2393 node2393 pivotPermutation2393; decide +kernel
  have hmoment : injectiveMoment H node2393 = injectiveMoment H pivotMatrix2393 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2393 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2393 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2393 (0 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2393 (0 : Fin 4) = raw5682 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2393 raw5682; decide +kernel
    rw [heq]
    exact (canonical5682 hH).trans (sound802 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2393 (1 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2393 (1 : Fin 4) = raw5612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2393 raw5612; decide +kernel
    rw [heq]
    exact (canonical5612 hH).trans (sound773 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2393 (2 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2393 (2 : Fin 4) = raw5600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2393 raw5600; decide +kernel
    rw [heq]
    exact (canonical5600 hH).trans (sound769 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2393 (3 : Fin 4)) =
      Sparse.eval value768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2393 (3 : Fin 4) = raw5599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2393 raw5599; decide +kernel
    rw [heq]
    exact (canonical5599 hH).trans (sound768 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2393 + (injectiveMoment H (mergeFirst pivotMatrix2393 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2393 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2393 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2393 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2393, value768, value769, value773, value802, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2394 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2394 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2394 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2394 = Sparse.eval value2394 (momentVector H) := by
  have heq : pivotMatrix2394 = (fun u v => node2394 (pivotPermutation2394 u) v) := by apply Matrix.ext; unfold pivotMatrix2394 node2394 pivotPermutation2394; decide +kernel
  have hmoment : injectiveMoment H node2394 = injectiveMoment H pivotMatrix2394 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2394 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2394 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2394 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2394 (0 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2394 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2394 (1 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2394 (1 : Fin 4) = raw5613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2394 raw5613; decide +kernel
    rw [heq]
    exact (canonical5613 hH).trans (sound774 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2394 (2 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2394 (2 : Fin 4) = raw5601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2394 raw5601; decide +kernel
    rw [heq]
    exact (canonical5601 hH).trans (sound915 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2394 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2394 (3 : Fin 4) = raw5600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2394 raw5600; decide +kernel
    rw [heq]
    exact (canonical5600 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2394 + (injectiveMoment H (mergeFirst pivotMatrix2394 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2394 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2394 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2394 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2394, value769, value774, value915, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2395 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2395 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2395 = Sparse.eval value2395 (momentVector H) := by
  have heq : pivotMatrix2395 = (fun u v => node2395 (pivotPermutation2395 u) v) := by apply Matrix.ext; unfold pivotMatrix2395 node2395 pivotPermutation2395; decide +kernel
  have hmoment : injectiveMoment H node2395 = injectiveMoment H pivotMatrix2395 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2395 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2395 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2395 (0 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2395 (0 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2395 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2395 (1 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2395 (1 : Fin 4) = raw5614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2395 raw5614; decide +kernel
    rw [heq]
    exact (canonical5614 hH).trans (sound775 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2395 (2 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2395 (2 : Fin 4) = raw5602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2395 raw5602; decide +kernel
    rw [heq]
    exact (canonical5602 hH).trans (sound1177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2395 (3 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2395 (3 : Fin 4) = raw5601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2395 raw5601; decide +kernel
    rw [heq]
    exact (canonical5601 hH).trans (sound915 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2395 + (injectiveMoment H (mergeFirst pivotMatrix2395 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2395 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2395 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2395 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2395, value1177, value1221, value775, value915, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2396 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2396 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem sound2396 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2396 = Sparse.eval value2396 (momentVector H) := by
  have heq : pivotMatrix2396 = (fun u v => node2396 (pivotPermutation2396 u) v) := by apply Matrix.ext; unfold pivotMatrix2396 node2396 pivotPermutation2396; decide +kernel
  have hmoment : injectiveMoment H node2396 = injectiveMoment H pivotMatrix2396 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2396 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2396 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2396 (0 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2396 (0 : Fin 4) = raw5691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2396 raw5691; decide +kernel
    rw [heq]
    exact (canonical5691 hH).trans (sound802 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2396 (1 : Fin 4)) =
      Sparse.eval value780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2396 (1 : Fin 4) = raw5616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2396 raw5616; decide +kernel
    rw [heq]
    exact (canonical5616 hH).trans (sound780 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2396 (2 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2396 (2 : Fin 4) = raw5611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2396 raw5611; decide +kernel
    rw [heq]
    exact (canonical5611 hH).trans (sound772 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2396 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2396 (3 : Fin 4) = raw5610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2396 raw5610; decide +kernel
    rw [heq]
    exact (canonical5610 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2396 + (injectiveMoment H (mergeFirst pivotMatrix2396 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2396 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2396 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2396 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2396, value769, value772, value780, value802, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2397 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2397 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound2397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2397 = Sparse.eval value2397 (momentVector H) := by
  have heq : pivotMatrix2397 = (fun u v => node2397 (pivotPermutation2397 u) v) := by apply Matrix.ext; unfold pivotMatrix2397 node2397 pivotPermutation2397; decide +kernel
  have hmoment : injectiveMoment H node2397 = injectiveMoment H pivotMatrix2397 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2397 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2397 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2397 (0 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2397 (0 : Fin 4) = raw5692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2397 raw5692; decide +kernel
    rw [heq]
    exact (canonical5692 hH).trans (sound806 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2397 (1 : Fin 4)) =
      Sparse.eval value781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2397 (1 : Fin 4) = raw5617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2397 raw5617; decide +kernel
    rw [heq]
    exact (canonical5617 hH).trans (sound781 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2397 (2 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2397 (2 : Fin 4) = raw5613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2397 raw5613; decide +kernel
    rw [heq]
    exact (canonical5613 hH).trans (sound774 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2397 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2397 (3 : Fin 4) = raw5612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2397 raw5612; decide +kernel
    rw [heq]
    exact (canonical5612 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2397 + (injectiveMoment H (mergeFirst pivotMatrix2397 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2397 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2397 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2397 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2397, value773, value774, value781, value806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2398 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2398 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound2398 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2398 = Sparse.eval value2398 (momentVector H) := by
  have heq : pivotMatrix2398 = (fun u v => node2398 (pivotPermutation2398 u) v) := by apply Matrix.ext; unfold pivotMatrix2398 node2398 pivotPermutation2398; decide +kernel
  have hmoment : injectiveMoment H node2398 = injectiveMoment H pivotMatrix2398 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2398 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2398 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2398 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2398 (0 : Fin 4) = raw5693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2398 raw5693; decide +kernel
    rw [heq]
    exact (canonical5693 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2398 (1 : Fin 4)) =
      Sparse.eval value782 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2398 (1 : Fin 4) = raw5618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2398 raw5618; decide +kernel
    rw [heq]
    exact (canonical5618 hH).trans (sound782 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2398 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2398 (2 : Fin 4) = raw5614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2398 raw5614; decide +kernel
    rw [heq]
    exact (canonical5614 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2398 (3 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2398 (3 : Fin 4) = raw5613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2398 raw5613; decide +kernel
    rw [heq]
    exact (canonical5613 hH).trans (sound774 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2398 + (injectiveMoment H (mergeFirst pivotMatrix2398 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2398 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2398 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2398 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2398, value774, value775, value782, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2399 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2399 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound2399 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2399 = Sparse.eval value2399 (momentVector H) := by
  have heq : pivotMatrix2399 = (fun u v => node2399 (pivotPermutation2399 u) v) := by apply Matrix.ext; unfold pivotMatrix2399 node2399 pivotPermutation2399; decide +kernel
  have hmoment : injectiveMoment H node2399 = injectiveMoment H pivotMatrix2399 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2399 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2399 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2399 (0 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2399 (0 : Fin 4) = raw5708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2399 raw5708; decide +kernel
    rw [heq]
    exact (canonical5708 hH).trans (sound1043 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2399 (1 : Fin 4)) =
      Sparse.eval value906 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2399 (1 : Fin 4) = raw5625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2399 raw5625; decide +kernel
    rw [heq]
    exact (canonical5625 hH).trans (sound906 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2399 (2 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2399 (2 : Fin 4) = raw5622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2399 raw5622; decide +kernel
    rw [heq]
    exact (canonical5622 hH).trans (sound786 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2399 (3 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2399 (3 : Fin 4) = raw5621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2399 raw5621; decide +kernel
    rw [heq]
    exact (canonical5621 hH).trans (sound1042 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2399 + (injectiveMoment H (mergeFirst pivotMatrix2399 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2399 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2399 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2399 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2399, value1042, value1043, value786, value906, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2400 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2400 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2400 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2400 = Sparse.eval value2400 (momentVector H) := by
  have heq : pivotMatrix2400 = (fun u v => node2400 (pivotPermutation2400 u) v) := by apply Matrix.ext; unfold pivotMatrix2400 node2400 pivotPermutation2400; decide +kernel
  have hmoment : injectiveMoment H node2400 = injectiveMoment H pivotMatrix2400 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2400 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2400 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2400 (0 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2400 (0 : Fin 4) = raw5709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2400 raw5709; decide +kernel
    rw [heq]
    exact (canonical5709 hH).trans (sound1203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2400 (1 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2400 (1 : Fin 4) = raw5626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2400 raw5626; decide +kernel
    rw [heq]
    exact (canonical5626 hH).trans (sound910 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2400 (2 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2400 (2 : Fin 4) = raw5623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2400 raw5623; decide +kernel
    rw [heq]
    exact (canonical5623 hH).trans (sound1171 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2400 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2400 (3 : Fin 4) = raw5622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2400 raw5622; decide +kernel
    rw [heq]
    exact (canonical5622 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2400 + (injectiveMoment H (mergeFirst pivotMatrix2400 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2400 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2400 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2400 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2400, value1171, value1203, value786, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2401 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2401 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2401 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2401 = Sparse.eval value2401 (momentVector H) := by
  have heq : pivotMatrix2401 = (fun u v => node2401 (pivotPermutation2401 u) v) := by apply Matrix.ext; unfold pivotMatrix2401 node2401 pivotPermutation2401; decide +kernel
  have hmoment : injectiveMoment H node2401 = injectiveMoment H pivotMatrix2401 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2401 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2401 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2401 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2401 (0 : Fin 4) = raw5714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2401 raw5714; decide +kernel
    rw [heq]
    exact (canonical5714 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2401 (1 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2401 (1 : Fin 4) = raw5630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2401 raw5630; decide +kernel
    rw [heq]
    exact (canonical5630 hH).trans (sound787 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2401 (2 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2401 (2 : Fin 4) = raw5627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2401 raw5627; decide +kernel
    rw [heq]
    exact (canonical5627 hH).trans (sound1170 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2401 (3 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2401 (3 : Fin 4) = raw5626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2401 raw5626; decide +kernel
    rw [heq]
    exact (canonical5626 hH).trans (sound910 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2401 + (injectiveMoment H (mergeFirst pivotMatrix2401 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2401 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2401 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2401 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2401, value1170, value1202, value787, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2402 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2402 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2402 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2402 = Sparse.eval value2402 (momentVector H) := by
  have heq : pivotMatrix2402 = (fun u v => node2402 (pivotPermutation2402 u) v) := by apply Matrix.ext; unfold pivotMatrix2402 node2402 pivotPermutation2402; decide +kernel
  have hmoment : injectiveMoment H node2402 = injectiveMoment H pivotMatrix2402 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2402 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2402 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2402 (0 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2402 (0 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2402 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2402 (1 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2402 (1 : Fin 4) = raw5629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2402 raw5629; decide +kernel
    rw [heq]
    exact (canonical5629 hH).trans (sound910 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2402 (2 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2402 (2 : Fin 4) = raw5613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2402 raw5613; decide +kernel
    rw [heq]
    exact (canonical5613 hH).trans (sound774 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2402 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2402 (3 : Fin 4) = raw5610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2402 raw5610; decide +kernel
    rw [heq]
    exact (canonical5610 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2402 + (injectiveMoment H (mergeFirst pivotMatrix2402 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2402 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2402 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2402 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2402, value769, value774, value910, value915, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2403 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2403 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2403 = Sparse.eval value2403 (momentVector H) := by
  have heq : pivotMatrix2403 = (fun u v => node2403 (pivotPermutation2403 u) v) := by apply Matrix.ext; unfold pivotMatrix2403 node2403 pivotPermutation2403; decide +kernel
  have hmoment : injectiveMoment H node2403 = injectiveMoment H pivotMatrix2403 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2403 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2403 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2403 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2403 (0 : Fin 4) = raw6288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2403 raw6288; decide +kernel
    rw [heq]
    exact (canonical6288 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2403 (1 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2403 (1 : Fin 4) = raw5632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2403 raw5632; decide +kernel
    rw [heq]
    exact (canonical5632 hH).trans (sound1170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2403 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2403 (2 : Fin 4) = raw5614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2403 raw5614; decide +kernel
    rw [heq]
    exact (canonical5614 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2403 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2403 (3 : Fin 4) = raw5610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2403 raw5610; decide +kernel
    rw [heq]
    exact (canonical5610 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2403 + (injectiveMoment H (mergeFirst pivotMatrix2403 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2403 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2403 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2403 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2403, value1170, value769, value775, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2404 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2404 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, 2, 0, -3]]

theorem sound2404 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2404 = Sparse.eval value2404 (momentVector H) := by
  have heq : pivotMatrix2404 = (fun u v => node2404 (pivotPermutation2404 u) v) := by apply Matrix.ext; unfold pivotMatrix2404 node2404 pivotPermutation2404; decide +kernel
  have hmoment : injectiveMoment H node2404 = injectiveMoment H pivotMatrix2404 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2404 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2404 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2404 (0 : Fin 4)) =
      Sparse.eval value796 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2404 (0 : Fin 4) = raw5734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2404 raw5734; decide +kernel
    rw [heq]
    exact (canonical5734 hH).trans (sound796 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2404 (1 : Fin 4)) =
      Sparse.eval value1197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2404 (1 : Fin 4) = raw5655 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2404 raw5655; decide +kernel
    rw [heq]
    exact (canonical5655 hH).trans (sound1197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2404 (2 : Fin 4)) =
      Sparse.eval value789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2404 (2 : Fin 4) = raw5645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2404 raw5645; decide +kernel
    rw [heq]
    exact (canonical5645 hH).trans (sound789 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2404 (3 : Fin 4)) =
      Sparse.eval value760 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2404 (3 : Fin 4) = raw5644 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2404 raw5644; decide +kernel
    rw [heq]
    exact (canonical5644 hH).trans (sound760 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2404 + (injectiveMoment H (mergeFirst pivotMatrix2404 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2404 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2404 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2404 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2404, value1197, value760, value789, value796, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2405 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2405 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem sound2405 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2405 = Sparse.eval value2405 (momentVector H) := by
  have heq : pivotMatrix2405 = (fun u v => node2405 (pivotPermutation2405 u) v) := by apply Matrix.ext; unfold pivotMatrix2405 node2405 pivotPermutation2405; decide +kernel
  have hmoment : injectiveMoment H node2405 = injectiveMoment H pivotMatrix2405 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2405 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2405 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2405 (0 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2405 (0 : Fin 4) = raw6430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2405 raw6430; decide +kernel
    rw [heq]
    exact (canonical6430 hH).trans (sound1032 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2405 (1 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2405 (1 : Fin 4) = raw5701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2405 raw5701; decide +kernel
    rw [heq]
    exact (canonical5701 hH).trans (sound799 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2405 (2 : Fin 4)) =
      Sparse.eval value793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2405 (2 : Fin 4) = raw5648 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2405 raw5648; decide +kernel
    rw [heq]
    exact (canonical5648 hH).trans (sound793 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2405 (3 : Fin 4)) =
      Sparse.eval value763 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2405 (3 : Fin 4) = raw5646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2405 raw5646; decide +kernel
    rw [heq]
    exact (canonical5646 hH).trans (sound763 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2405 + (injectiveMoment H (mergeFirst pivotMatrix2405 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2405 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2405 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2405 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2405, value1032, value763, value793, value799, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2406 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2406 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound2406 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2406 = Sparse.eval value2406 (momentVector H) := by
  have heq : pivotMatrix2406 = (fun u v => node2406 (pivotPermutation2406 u) v) := by apply Matrix.ext; unfold pivotMatrix2406 node2406 pivotPermutation2406; decide +kernel
  have hmoment : injectiveMoment H node2406 = injectiveMoment H pivotMatrix2406 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2406 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2406 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2406 (0 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (0 : Fin 4) = raw6431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw6431; decide +kernel
    rw [heq]
    exact (canonical6431 hH).trans (sound1032 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2406 (1 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (1 : Fin 4) = raw5703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw5703; decide +kernel
    rw [heq]
    exact (canonical5703 hH).trans (sound816 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2406 (2 : Fin 4)) =
      Sparse.eval value795 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (2 : Fin 4) = raw5649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw5649; decide +kernel
    rw [heq]
    exact (canonical5649 hH).trans (sound795 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2406 (3 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2406 (3 : Fin 4) = raw5647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2406 raw5647; decide +kernel
    rw [heq]
    exact (canonical5647 hH).trans (sound791 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2406 + (injectiveMoment H (mergeFirst pivotMatrix2406 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2406 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2406 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2406 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2406, value1032, value791, value795, value816, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2407 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2407 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

theorem sound2407 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2407 = Sparse.eval value2407 (momentVector H) := by
  have heq : pivotMatrix2407 = (fun u v => node2407 (pivotPermutation2407 u) v) := by apply Matrix.ext; unfold pivotMatrix2407 node2407 pivotPermutation2407; decide +kernel
  have hmoment : injectiveMoment H node2407 = injectiveMoment H pivotMatrix2407 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2407 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2407 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2407 (0 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2407 (0 : Fin 4) = raw5587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2407 raw5587; decide +kernel
    rw [heq]
    exact (canonical5587 hH).trans (sound907 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2407 (1 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2407 (1 : Fin 4) = raw5665 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2407 raw5665; decide +kernel
    rw [heq]
    exact (canonical5665 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2407 (2 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2407 (2 : Fin 4) = raw5669 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2407 raw5669; decide +kernel
    rw [heq]
    exact (canonical5669 hH).trans (sound272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2407 (3 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2407 (3 : Fin 4) = raw5674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2407 raw5674; decide +kernel
    rw [heq]
    exact (canonical5674 hH).trans (sound967 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2407 + (injectiveMoment H (mergeFirst pivotMatrix2407 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2407 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2407 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2407 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2407, value272, value907, value967, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2408 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2408 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound2408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2408 = Sparse.eval value2408 (momentVector H) := by
  have heq : pivotMatrix2408 = (fun u v => node2408 (pivotPermutation2408 u) v) := by apply Matrix.ext; unfold pivotMatrix2408 node2408 pivotPermutation2408; decide +kernel
  have hmoment : injectiveMoment H node2408 = injectiveMoment H pivotMatrix2408 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2408 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2408 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2408 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2408 (0 : Fin 4) = raw5600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2408 raw5600; decide +kernel
    rw [heq]
    exact (canonical5600 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2408 (1 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2408 (1 : Fin 4) = raw5666 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2408 raw5666; decide +kernel
    rw [heq]
    exact (canonical5666 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2408 (2 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2408 (2 : Fin 4) = raw5682 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2408 raw5682; decide +kernel
    rw [heq]
    exact (canonical5682 hH).trans (sound802 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2408 (3 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2408 (3 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2408 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2408 + (injectiveMoment H (mergeFirst pivotMatrix2408 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2408 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2408 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2408 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2408, value185, value769, value802, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2409 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2409 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2409 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2409 = Sparse.eval value2409 (momentVector H) := by
  have heq : pivotMatrix2409 = (fun u v => node2409 (pivotPermutation2409 u) v) := by apply Matrix.ext; unfold pivotMatrix2409 node2409 pivotPermutation2409; decide +kernel
  have hmoment : injectiveMoment H node2409 = injectiveMoment H pivotMatrix2409 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2409 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2409 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2409 (0 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2409 (0 : Fin 4) = raw5602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2409 raw5602; decide +kernel
    rw [heq]
    exact (canonical5602 hH).trans (sound1177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2409 (1 : Fin 4)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2409 (1 : Fin 4) = raw5667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2409 raw5667; decide +kernel
    rw [heq]
    exact (canonical5667 hH).trans (sound292 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2409 (2 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2409 (2 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2409 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2409 (3 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2409 (3 : Fin 4) = raw5685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2409 raw5685; decide +kernel
    rw [heq]
    exact (canonical5685 hH).trans (sound803 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2409 + (injectiveMoment H (mergeFirst pivotMatrix2409 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2409 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2409 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2409 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2409, value1177, value1221, value292, value803, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2410 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2410 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem sound2410 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2410 = Sparse.eval value2410 (momentVector H) := by
  have heq : pivotMatrix2410 = (fun u v => node2410 (pivotPermutation2410 u) v) := by apply Matrix.ext; unfold pivotMatrix2410 node2410 pivotPermutation2410; decide +kernel
  have hmoment : injectiveMoment H node2410 = injectiveMoment H pivotMatrix2410 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2410 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2410 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2410 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2410 (0 : Fin 4) = raw5609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2410 raw5609; decide +kernel
    rw [heq]
    exact (canonical5609 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2410 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2410 (1 : Fin 4) = raw5677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2410 raw5677; decide +kernel
    rw [heq]
    exact (canonical5677 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2410 (2 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2410 (2 : Fin 4) = raw5687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2410 raw5687; decide +kernel
    rw [heq]
    exact (canonical5687 hH).trans (sound804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2410 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2410 (3 : Fin 4) = raw5690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2410 raw5690; decide +kernel
    rw [heq]
    exact (canonical5690 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2410 + (injectiveMoment H (mergeFirst pivotMatrix2410 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2410 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2410 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2410 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2410, value1202, value771, value804, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2411 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2411 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem sound2411 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2411 = Sparse.eval value2411 (momentVector H) := by
  have heq : pivotMatrix2411 = (fun u v => node2411 (pivotPermutation2411 u) v) := by apply Matrix.ext; unfold pivotMatrix2411 node2411 pivotPermutation2411; decide +kernel
  have hmoment : injectiveMoment H node2411 = injectiveMoment H pivotMatrix2411 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2411 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2411 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2411 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2411 (0 : Fin 4) = raw5610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2411 raw5610; decide +kernel
    rw [heq]
    exact (canonical5610 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2411 (1 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2411 (1 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2411 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2411 (2 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2411 (2 : Fin 4) = raw5690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2411 raw5690; decide +kernel
    rw [heq]
    exact (canonical5690 hH).trans (sound805 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2411 (3 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2411 (3 : Fin 4) = raw5691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2411 raw5691; decide +kernel
    rw [heq]
    exact (canonical5691 hH).trans (sound802 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2411 + (injectiveMoment H (mergeFirst pivotMatrix2411 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2411 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2411 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2411 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2411, value769, value802, value805, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2412 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2412 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2412 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2412 = Sparse.eval value2412 (momentVector H) := by
  have heq : pivotMatrix2412 = (fun u v => node2412 (pivotPermutation2412 u) v) := by apply Matrix.ext; unfold pivotMatrix2412 node2412 pivotPermutation2412; decide +kernel
  have hmoment : injectiveMoment H node2412 = injectiveMoment H pivotMatrix2412 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2412 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2412 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2412 (0 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2412 (0 : Fin 4) = raw5613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2412 raw5613; decide +kernel
    rw [heq]
    exact (canonical5613 hH).trans (sound774 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2412 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2412 (1 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2412 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2412 (2 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2412 (2 : Fin 4) = raw5692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2412 raw5692; decide +kernel
    rw [heq]
    exact (canonical5692 hH).trans (sound806 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2412 (3 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2412 (3 : Fin 4) = raw5693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2412 raw5693; decide +kernel
    rw [heq]
    exact (canonical5693 hH).trans (sound807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2412 + (injectiveMoment H (mergeFirst pivotMatrix2412 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2412 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2412 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2412 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2412, value774, value806, value807, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2413 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2413 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2413 = Sparse.eval value2413 (momentVector H) := by
  have heq : pivotMatrix2413 = (fun u v => node2413 (pivotPermutation2413 u) v) := by apply Matrix.ext; unfold pivotMatrix2413 node2413 pivotPermutation2413; decide +kernel
  have hmoment : injectiveMoment H node2413 = injectiveMoment H pivotMatrix2413 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2413 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2413 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2413 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2413 (0 : Fin 4) = raw5614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2413 raw5614; decide +kernel
    rw [heq]
    exact (canonical5614 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2413 (1 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2413 (1 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2413 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2413 (2 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2413 (2 : Fin 4) = raw5693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2413 raw5693; decide +kernel
    rw [heq]
    exact (canonical5693 hH).trans (sound807 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2413 (3 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2413 (3 : Fin 4) = raw5694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2413 raw5694; decide +kernel
    rw [heq]
    exact (canonical5694 hH).trans (sound808 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2413 + (injectiveMoment H (mergeFirst pivotMatrix2413 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2413 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2413 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2413 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2413, value1221, value775, value807, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2414 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2414 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem sound2414 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2414 = Sparse.eval value2414 (momentVector H) := by
  have heq : pivotMatrix2414 = (fun u v => node2414 (pivotPermutation2414 u) v) := by apply Matrix.ext; unfold pivotMatrix2414 node2414 pivotPermutation2414; decide +kernel
  have hmoment : injectiveMoment H node2414 = injectiveMoment H pivotMatrix2414 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2414 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2414 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2414 (0 : Fin 4)) =
      Sparse.eval value961 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2414 (0 : Fin 4) = raw5620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2414 raw5620; decide +kernel
    rw [heq]
    exact (canonical5620 hH).trans (sound961 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2414 (1 : Fin 4)) =
      Sparse.eval value798 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2414 (1 : Fin 4) = raw5700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2414 raw5700; decide +kernel
    rw [heq]
    exact (canonical5700 hH).trans (sound798 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2414 (2 : Fin 4)) =
      Sparse.eval value798 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2414 (2 : Fin 4) = raw5706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2414 raw5706; decide +kernel
    rw [heq]
    exact (canonical5706 hH).trans (sound798 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2414 (3 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2414 (3 : Fin 4) = raw5707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2414 raw5707; decide +kernel
    rw [heq]
    exact (canonical5707 hH).trans (sound1041 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2414 + (injectiveMoment H (mergeFirst pivotMatrix2414 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2414 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2414 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2414 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2414, value1041, value798, value961, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2415 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2415 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem sound2415 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2415 = Sparse.eval value2415 (momentVector H) := by
  have heq : pivotMatrix2415 = (fun u v => node2415 (pivotPermutation2415 u) v) := by apply Matrix.ext; unfold pivotMatrix2415 node2415 pivotPermutation2415; decide +kernel
  have hmoment : injectiveMoment H node2415 = injectiveMoment H pivotMatrix2415 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2415 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2415 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2415 (0 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2415 (0 : Fin 4) = raw5621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2415 raw5621; decide +kernel
    rw [heq]
    exact (canonical5621 hH).trans (sound1042 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2415 (1 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2415 (1 : Fin 4) = raw5701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2415 raw5701; decide +kernel
    rw [heq]
    exact (canonical5701 hH).trans (sound799 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2415 (2 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2415 (2 : Fin 4) = raw5707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2415 raw5707; decide +kernel
    rw [heq]
    exact (canonical5707 hH).trans (sound1041 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2415 (3 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2415 (3 : Fin 4) = raw5708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2415 raw5708; decide +kernel
    rw [heq]
    exact (canonical5708 hH).trans (sound1043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2415 + (injectiveMoment H (mergeFirst pivotMatrix2415 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2415 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2415 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2415 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2415, value1041, value1042, value1043, value799, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2416 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2416 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound2416 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2416 = Sparse.eval value2416 (momentVector H) := by
  have heq : pivotMatrix2416 = (fun u v => node2416 (pivotPermutation2416 u) v) := by apply Matrix.ext; unfold pivotMatrix2416 node2416 pivotPermutation2416; decide +kernel
  have hmoment : injectiveMoment H node2416 = injectiveMoment H pivotMatrix2416 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2416 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2416 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2416 (0 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2416 (0 : Fin 4) = raw5623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2416 raw5623; decide +kernel
    rw [heq]
    exact (canonical5623 hH).trans (sound1171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2416 (1 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2416 (1 : Fin 4) = raw5703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2416 raw5703; decide +kernel
    rw [heq]
    exact (canonical5703 hH).trans (sound816 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2416 (2 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2416 (2 : Fin 4) = raw5709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2416 raw5709; decide +kernel
    rw [heq]
    exact (canonical5709 hH).trans (sound1203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2416 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2416 (3 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2416 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2416 + (injectiveMoment H (mergeFirst pivotMatrix2416 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2416 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2416 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2416 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2416, value1063, value1171, value1203, value816, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2417 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2417 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2417 = Sparse.eval value2417 (momentVector H) := by
  have heq : pivotMatrix2417 = (fun u v => node2417 (pivotPermutation2417 u) v) := by apply Matrix.ext; unfold pivotMatrix2417 node2417 pivotPermutation2417; decide +kernel
  have hmoment : injectiveMoment H node2417 = injectiveMoment H pivotMatrix2417 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2417 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2417 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2417 (0 : Fin 4)) =
      Sparse.eval value981 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2417 (0 : Fin 4) = raw5624 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2417 raw5624; decide +kernel
    rw [heq]
    exact (canonical5624 hH).trans (sound981 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2417 (1 : Fin 4)) =
      Sparse.eval value817 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2417 (1 : Fin 4) = raw5704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2417 raw5704; decide +kernel
    rw [heq]
    exact (canonical5704 hH).trans (sound817 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2417 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2417 (2 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2417 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2417 (3 : Fin 4)) =
      Sparse.eval value818 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2417 (3 : Fin 4) = raw5711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2417 raw5711; decide +kernel
    rw [heq]
    exact (canonical5711 hH).trans (sound818 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2417 + (injectiveMoment H (mergeFirst pivotMatrix2417 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2417 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2417 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2417 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2417, value1063, value817, value818, value981, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2418 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2418 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2418 = Sparse.eval value2418 (momentVector H) := by
  have heq : pivotMatrix2418 = (fun u v => node2418 (pivotPermutation2418 u) v) := by apply Matrix.ext; unfold pivotMatrix2418 node2418 pivotPermutation2418; decide +kernel
  have hmoment : injectiveMoment H node2418 = injectiveMoment H pivotMatrix2418 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2418 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2418 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2418 (0 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2418 (0 : Fin 4) = raw5627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2418 raw5627; decide +kernel
    rw [heq]
    exact (canonical5627 hH).trans (sound1170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2418 (1 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2418 (1 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2418 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2418 (2 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2418 (2 : Fin 4) = raw5714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2418 raw5714; decide +kernel
    rw [heq]
    exact (canonical5714 hH).trans (sound1202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2418 (3 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2418 (3 : Fin 4) = raw5715 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2418 raw5715; decide +kernel
    rw [heq]
    exact (canonical5715 hH).trans (sound819 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2418 + (injectiveMoment H (mergeFirst pivotMatrix2418 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2418 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2418 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2418 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2418, value1063, value1170, value1202, value819, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2419 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2419 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem sound2419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2419 = Sparse.eval value2419 (momentVector H) := by
  have heq : pivotMatrix2419 = (fun u v => node2419 (pivotPermutation2419 u) v) := by apply Matrix.ext; unfold pivotMatrix2419 node2419 pivotPermutation2419; decide +kernel
  have hmoment : injectiveMoment H node2419 = injectiveMoment H pivotMatrix2419 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2419 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2419 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2419 (0 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2419 (0 : Fin 4) = raw5765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2419 raw5765; decide +kernel
    rw [heq]
    exact (canonical5765 hH).trans (sound1260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2419 (1 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2419 (1 : Fin 4) = raw5690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2419 raw5690; decide +kernel
    rw [heq]
    exact (canonical5690 hH).trans (sound805 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2419 (2 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2419 (2 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2419 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2419 (3 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2419 (3 : Fin 4) = raw5677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2419 raw5677; decide +kernel
    rw [heq]
    exact (canonical5677 hH).trans (sound1202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2419 + (injectiveMoment H (mergeFirst pivotMatrix2419 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2419 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2419 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2419 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2419, value1202, value1260, value805, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2420 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2420 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem sound2420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2420 = Sparse.eval value2420 (momentVector H) := by
  have heq : pivotMatrix2420 = (fun u v => node2420 (pivotPermutation2420 u) v) := by apply Matrix.ext; unfold pivotMatrix2420 node2420 pivotPermutation2420; decide +kernel
  have hmoment : injectiveMoment H node2420 = injectiveMoment H pivotMatrix2420 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2420 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2420 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2420 (0 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2420 (0 : Fin 4) = raw5766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2420 raw5766; decide +kernel
    rw [heq]
    exact (canonical5766 hH).trans (sound1047 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2420 (1 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2420 (1 : Fin 4) = raw5691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2420 raw5691; decide +kernel
    rw [heq]
    exact (canonical5691 hH).trans (sound802 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2420 (2 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2420 (2 : Fin 4) = raw5681 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2420 raw5681; decide +kernel
    rw [heq]
    exact (canonical5681 hH).trans (sound801 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2420 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2420 (3 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2420 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2420 + (injectiveMoment H (mergeFirst pivotMatrix2420 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2420 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2420 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2420 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2420, value1047, value801, value802, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2421 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2421 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound2421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2421 = Sparse.eval value2421 (momentVector H) := by
  have heq : pivotMatrix2421 = (fun u v => node2421 (pivotPermutation2421 u) v) := by apply Matrix.ext; unfold pivotMatrix2421 node2421 pivotPermutation2421; decide +kernel
  have hmoment : injectiveMoment H node2421 = injectiveMoment H pivotMatrix2421 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2421 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2421 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2421 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2421 (0 : Fin 4) = raw5768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2421 raw5768; decide +kernel
    rw [heq]
    exact (canonical5768 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2421 (1 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2421 (1 : Fin 4) = raw5692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2421 raw5692; decide +kernel
    rw [heq]
    exact (canonical5692 hH).trans (sound806 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2421 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2421 (2 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2421 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2421 (3 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2421 (3 : Fin 4) = raw5682 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2421 raw5682; decide +kernel
    rw [heq]
    exact (canonical5682 hH).trans (sound802 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2421 + (injectiveMoment H (mergeFirst pivotMatrix2421 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2421 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2421 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2421 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2421, value1053, value802, value806, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2422 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2422 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound2422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2422 = Sparse.eval value2422 (momentVector H) := by
  have heq : pivotMatrix2422 = (fun u v => node2422 (pivotPermutation2422 u) v) := by apply Matrix.ext; unfold pivotMatrix2422 node2422 pivotPermutation2422; decide +kernel
  have hmoment : injectiveMoment H node2422 = injectiveMoment H pivotMatrix2422 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2422 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2422 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2422 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2422 (0 : Fin 4) = raw5769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2422 raw5769; decide +kernel
    rw [heq]
    exact (canonical5769 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2422 (1 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2422 (1 : Fin 4) = raw5693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2422 raw5693; decide +kernel
    rw [heq]
    exact (canonical5693 hH).trans (sound807 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2422 (2 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2422 (2 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2422 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2422 (3 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2422 (3 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2422 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2422 + (injectiveMoment H (mergeFirst pivotMatrix2422 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2422 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2422 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2422 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2422, value1221, value1265, value807, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2423 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2423 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem sound2423 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2423 = Sparse.eval value2423 (momentVector H) := by
  have heq : pivotMatrix2423 = (fun u v => node2423 (pivotPermutation2423 u) v) := by apply Matrix.ext; unfold pivotMatrix2423 node2423 pivotPermutation2423; decide +kernel
  have hmoment : injectiveMoment H node2423 = injectiveMoment H pivotMatrix2423 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2423 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2423 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2423 (0 : Fin 4)) =
      Sparse.eval value840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2423 (0 : Fin 4) = raw5770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2423 raw5770; decide +kernel
    rw [heq]
    exact (canonical5770 hH).trans (sound840 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2423 (1 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2423 (1 : Fin 4) = raw5694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2423 raw5694; decide +kernel
    rw [heq]
    exact (canonical5694 hH).trans (sound808 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2423 (2 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2423 (2 : Fin 4) = raw5685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2423 raw5685; decide +kernel
    rw [heq]
    exact (canonical5685 hH).trans (sound803 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2423 (3 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2423 (3 : Fin 4) = raw5684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2423 raw5684; decide +kernel
    rw [heq]
    exact (canonical5684 hH).trans (sound1221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2423 + (injectiveMoment H (mergeFirst pivotMatrix2423 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2423 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2423 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2423 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2423, value1221, value803, value808, value840, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2424 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2424 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem sound2424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2424 = Sparse.eval value2424 (momentVector H) := by
  have heq : pivotMatrix2424 = (fun u v => node2424 (pivotPermutation2424 u) v) := by apply Matrix.ext; unfold pivotMatrix2424 node2424 pivotPermutation2424; decide +kernel
  have hmoment : injectiveMoment H node2424 = injectiveMoment H pivotMatrix2424 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2424 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2424 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2424 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2424 (0 : Fin 4) = raw5782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2424 raw5782; decide +kernel
    rw [heq]
    exact (canonical5782 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2424 (1 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2424 (1 : Fin 4) = raw5713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2424 raw5713; decide +kernel
    rw [heq]
    exact (canonical5713 hH).trans (sound1043 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2424 (2 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2424 (2 : Fin 4) = raw5708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2424 raw5708; decide +kernel
    rw [heq]
    exact (canonical5708 hH).trans (sound1043 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2424 (3 : Fin 4)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2424 (3 : Fin 4) = raw5707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2424 raw5707; decide +kernel
    rw [heq]
    exact (canonical5707 hH).trans (sound1041 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2424 + (injectiveMoment H (mergeFirst pivotMatrix2424 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2424 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2424 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2424 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2424, value1040, value1041, value1043, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2425 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2425 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2425 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2425 = Sparse.eval value2425 (momentVector H) := by
  have heq : pivotMatrix2425 = (fun u v => node2425 (pivotPermutation2425 u) v) := by apply Matrix.ext; unfold pivotMatrix2425 node2425 pivotPermutation2425; decide +kernel
  have hmoment : injectiveMoment H node2425 = injectiveMoment H pivotMatrix2425 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2425 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2425 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2425 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2425 (0 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2425 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2425 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2425 (1 : Fin 4) = raw5714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2425 raw5714; decide +kernel
    rw [heq]
    exact (canonical5714 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2425 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2425 (2 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2425 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2425 (3 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2425 (3 : Fin 4) = raw5709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2425 raw5709; decide +kernel
    rw [heq]
    exact (canonical5709 hH).trans (sound1203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2425 + (injectiveMoment H (mergeFirst pivotMatrix2425 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2425 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2425 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2425 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2425, value1063, value1110, value1202, value1203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2426 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2426 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2426 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2426 = Sparse.eval value2426 (momentVector H) := by
  have heq : pivotMatrix2426 = (fun u v => node2426 (pivotPermutation2426 u) v) := by apply Matrix.ext; unfold pivotMatrix2426 node2426 pivotPermutation2426; decide +kernel
  have hmoment : injectiveMoment H node2426 = injectiveMoment H pivotMatrix2426 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2426 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2426 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2426 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2426 (0 : Fin 4) = raw6498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2426 raw6498; decide +kernel
    rw [heq]
    exact (canonical6498 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2426 (1 : Fin 4)) =
      Sparse.eval value816 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2426 (1 : Fin 4) = raw5719 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2426 raw5719; decide +kernel
    rw [heq]
    exact (canonical5719 hH).trans (sound816 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2426 (2 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2426 (2 : Fin 4) = raw5692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2426 raw5692; decide +kernel
    rw [heq]
    exact (canonical5692 hH).trans (sound806 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2426 (3 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2426 (3 : Fin 4) = raw5687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2426 raw5687; decide +kernel
    rw [heq]
    exact (canonical5687 hH).trans (sound804 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2426 + (injectiveMoment H (mergeFirst pivotMatrix2426 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2426 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2426 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2426 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2426, value1053, value804, value806, value816, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2427 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2427 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2427 = Sparse.eval value2427 (momentVector H) := by
  have heq : pivotMatrix2427 = (fun u v => node2427 (pivotPermutation2427 u) v) := by apply Matrix.ext; unfold pivotMatrix2427 node2427 pivotPermutation2427; decide +kernel
  have hmoment : injectiveMoment H node2427 = injectiveMoment H pivotMatrix2427 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2427 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2427 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2427 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2427 (0 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2427 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2427 (1 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2427 (1 : Fin 4) = raw5716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2427 raw5716; decide +kernel
    rw [heq]
    exact (canonical5716 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2427 (2 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2427 (2 : Fin 4) = raw5692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2427 raw5692; decide +kernel
    rw [heq]
    exact (canonical5692 hH).trans (sound806 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2427 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2427 (3 : Fin 4) = raw5690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2427 raw5690; decide +kernel
    rw [heq]
    exact (canonical5690 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2427 + (injectiveMoment H (mergeFirst pivotMatrix2427 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2427 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2427 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2427 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2427, value1203, value805, value806, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2428 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2428 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2428 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2428 = Sparse.eval value2428 (momentVector H) := by
  have heq : pivotMatrix2428 = (fun u v => node2428 (pivotPermutation2428 u) v) := by apply Matrix.ext; unfold pivotMatrix2428 node2428 pivotPermutation2428; decide +kernel
  have hmoment : injectiveMoment H node2428 = injectiveMoment H pivotMatrix2428 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2428 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2428 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2428 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2428 (0 : Fin 4) = raw6288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2428 raw6288; decide +kernel
    rw [heq]
    exact (canonical6288 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2428 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2428 (1 : Fin 4) = raw5717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2428 raw5717; decide +kernel
    rw [heq]
    exact (canonical5717 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2428 (2 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2428 (2 : Fin 4) = raw5693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2428 raw5693; decide +kernel
    rw [heq]
    exact (canonical5693 hH).trans (sound807 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2428 (3 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2428 (3 : Fin 4) = raw5691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2428 raw5691; decide +kernel
    rw [heq]
    exact (canonical5691 hH).trans (sound802 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2428 + (injectiveMoment H (mergeFirst pivotMatrix2428 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2428 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2428 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2428 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2428, value1202, value802, value807, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2429 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2429 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem sound2429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2429 = Sparse.eval value2429 (momentVector H) := by
  have heq : pivotMatrix2429 = (fun u v => node2429 (pivotPermutation2429 u) v) := by apply Matrix.ext; unfold pivotMatrix2429 node2429 pivotPermutation2429; decide +kernel
  have hmoment : injectiveMoment H node2429 = injectiveMoment H pivotMatrix2429 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2429 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2429 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2429 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2429 (0 : Fin 4) = raw6505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2429 raw6505; decide +kernel
    rw [heq]
    exact (canonical6505 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2429 (1 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2429 (1 : Fin 4) = raw5721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2429 raw5721; decide +kernel
    rw [heq]
    exact (canonical5721 hH).trans (sound819 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2429 (2 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2429 (2 : Fin 4) = raw5694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2429 raw5694; decide +kernel
    rw [heq]
    exact (canonical5694 hH).trans (sound808 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2429 (3 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2429 (3 : Fin 4) = raw5691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2429 raw5691; decide +kernel
    rw [heq]
    exact (canonical5691 hH).trans (sound802 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2429 + (injectiveMoment H (mergeFirst pivotMatrix2429 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2429 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2429 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2429 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2429, value1053, value802, value808, value819, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2430 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2430 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem sound2430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2430 = Sparse.eval value2430 (momentVector H) := by
  have heq : pivotMatrix2430 = (fun u v => node2430 (pivotPermutation2430 u) v) := by apply Matrix.ext; unfold pivotMatrix2430 node2430 pivotPermutation2430; decide +kernel
  have hmoment : injectiveMoment H node2430 = injectiveMoment H pivotMatrix2430 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2430 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2430 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2430 (0 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2430 (0 : Fin 4) = raw6295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2430 raw6295; decide +kernel
    rw [heq]
    exact (canonical6295 hH).trans (sound978 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2430 (1 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2430 (1 : Fin 4) = raw5720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2430 raw5720; decide +kernel
    rw [heq]
    exact (canonical5720 hH).trans (sound1063 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2430 (2 : Fin 4)) =
      Sparse.eval value811 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2430 (2 : Fin 4) = raw5698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2430 raw5698; decide +kernel
    rw [heq]
    exact (canonical5698 hH).trans (sound811 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2430 (3 : Fin 4)) =
      Sparse.eval value810 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2430 (3 : Fin 4) = raw5697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2430 raw5697; decide +kernel
    rw [heq]
    exact (canonical5697 hH).trans (sound810 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2430 + (injectiveMoment H (mergeFirst pivotMatrix2430 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2430 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2430 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2430 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2430, value1063, value810, value811, value978, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2431 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2431 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2431 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2431 = Sparse.eval value2431 (momentVector H) := by
  have heq : pivotMatrix2431 = (fun u v => node2431 (pivotPermutation2431 u) v) := by apply Matrix.ext; unfold pivotMatrix2431 node2431 pivotPermutation2431; decide +kernel
  have hmoment : injectiveMoment H node2431 = injectiveMoment H pivotMatrix2431 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2431 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2431 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2431 (0 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2431 (0 : Fin 4) = raw5823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2431 raw5823; decide +kernel
    rw [heq]
    exact (canonical5823 hH).trans (sound854 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2431 (1 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2431 (1 : Fin 4) = raw5754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2431 raw5754; decide +kernel
    rw [heq]
    exact (canonical5754 hH).trans (sound1284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2431 (2 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2431 (2 : Fin 4) = raw5739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2431 raw5739; decide +kernel
    rw [heq]
    exact (canonical5739 hH).trans (sound832 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2431 (3 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2431 (3 : Fin 4) = raw5738 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2431 raw5738; decide +kernel
    rw [heq]
    exact (canonical5738 hH).trans (sound831 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2431 + (injectiveMoment H (mergeFirst pivotMatrix2431 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2431 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2431 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2431 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2431, value1284, value831, value832, value854, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
