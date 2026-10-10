import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical207
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical261

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2560 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2560 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem sound2560 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2560 = Sparse.eval value2560 (momentVector H) := by
  have heq : pivotMatrix2560 = (fun u v => node2560 (pivotPermutation2560 u) v) := by apply Matrix.ext; unfold pivotMatrix2560 node2560 pivotPermutation2560; decide +kernel
  have hmoment : injectiveMoment H node2560 = injectiveMoment H pivotMatrix2560 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2560 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2560 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2560 (0 : Fin 4)) =
      Sparse.eval value1225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2560 (0 : Fin 4) = raw7107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2560 raw7107; decide +kernel
    rw [heq]
    exact (canonical7107 hH).trans (sound1225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2560 (1 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2560 (1 : Fin 4) = raw6327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2560 raw6327; decide +kernel
    rw [heq]
    exact (canonical6327 hH).trans (sound1268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2560 (2 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2560 (2 : Fin 4) = raw6297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2560 raw6297; decide +kernel
    rw [heq]
    exact (canonical6297 hH).trans (sound979 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2560 (3 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2560 (3 : Fin 4) = raw6295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2560 raw6295; decide +kernel
    rw [heq]
    exact (canonical6295 hH).trans (sound978 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2560 + (injectiveMoment H (mergeFirst pivotMatrix2560 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2560 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2560 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2560 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2560, value1225, value1268, value978, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2561 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2561 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem sound2561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2561 = Sparse.eval value2561 (momentVector H) := by
  have heq : pivotMatrix2561 = (fun u v => node2561 (pivotPermutation2561 u) v) := by apply Matrix.ext; unfold pivotMatrix2561 node2561 pivotPermutation2561; decide +kernel
  have hmoment : injectiveMoment H node2561 = injectiveMoment H pivotMatrix2561 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2561 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2561 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2561 (0 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2561 (0 : Fin 4) = raw8055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2561 raw8055; decide +kernel
    rw [heq]
    exact (canonical8055 hH).trans (sound1155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2561 (1 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2561 (1 : Fin 4) = raw6392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2561 raw6392; decide +kernel
    rw [heq]
    exact (canonical6392 hH).trans (sound996 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2561 (2 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2561 (2 : Fin 4) = raw6347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2561 raw6347; decide +kernel
    rw [heq]
    exact (canonical6347 hH).trans (sound996 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2561 (3 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2561 (3 : Fin 4) = raw6344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2561 raw6344; decide +kernel
    rw [heq]
    exact (canonical6344 hH).trans (sound997 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2561 + (injectiveMoment H (mergeFirst pivotMatrix2561 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2561 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2561 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2561 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2561, value1155, value996, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2562 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem sound2562 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2562 = Sparse.eval value2562 (momentVector H) := by
  have heq : pivotMatrix2562 = (fun u v => node2562 (pivotPermutation2562 u) v) := by apply Matrix.ext; unfold pivotMatrix2562 node2562 pivotPermutation2562; decide +kernel
  have hmoment : injectiveMoment H node2562 = injectiveMoment H pivotMatrix2562 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2562 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2562 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2562 (0 : Fin 4)) =
      Sparse.eval value492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2562 (0 : Fin 4) = raw2089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2562 raw2089; decide +kernel
    rw [heq]
    exact (canonical2089 hH).trans (sound492 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2562 (1 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2562 (1 : Fin 4) = raw6377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2562 raw6377; decide +kernel
    rw [heq]
    exact (canonical6377 hH).trans (sound680 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2562 (2 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2562 (2 : Fin 4) = raw6547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2562 raw6547; decide +kernel
    rw [heq]
    exact (canonical6547 hH).trans (sound950 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2562 (3 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2562 (3 : Fin 4) = raw6551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2562 raw6551; decide +kernel
    rw [heq]
    exact (canonical6551 hH).trans (sound1074 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2562 + (injectiveMoment H (mergeFirst pivotMatrix2562 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2562 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2562 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2562 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2562, value1074, value492, value680, value950, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2563 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem sound2563 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2563 = Sparse.eval value2563 (momentVector H) := by
  have heq : pivotMatrix2563 = (fun u v => node2563 (pivotPermutation2563 u) v) := by apply Matrix.ext; unfold pivotMatrix2563 node2563 pivotPermutation2563; decide +kernel
  have hmoment : injectiveMoment H node2563 = injectiveMoment H pivotMatrix2563 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2563 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2563 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2563 (0 : Fin 4)) =
      Sparse.eval value1106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2563 (0 : Fin 4) = raw2093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2563 raw2093; decide +kernel
    rw [heq]
    exact (canonical2093 hH).trans (sound1106 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2563 (1 : Fin 4)) =
      Sparse.eval value1105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2563 (1 : Fin 4) = raw6378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2563 raw6378; decide +kernel
    rw [heq]
    exact (canonical6378 hH).trans (sound1105 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2563 (2 : Fin 4)) =
      Sparse.eval value779 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2563 (2 : Fin 4) = raw6553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2563 raw6553; decide +kernel
    rw [heq]
    exact (canonical6553 hH).trans (sound779 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2563 (3 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2563 (3 : Fin 4) = raw6554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2563 raw6554; decide +kernel
    rw [heq]
    exact (canonical6554 hH).trans (sound1075 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2563 + (injectiveMoment H (mergeFirst pivotMatrix2563 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2563 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2563 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2563 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2563, value1075, value1105, value1106, value779, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2564 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2564 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2564 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2564 = Sparse.eval value2564 (momentVector H) := by
  have heq : pivotMatrix2564 = (fun u v => node2564 (pivotPermutation2564 u) v) := by apply Matrix.ext; unfold pivotMatrix2564 node2564 pivotPermutation2564; decide +kernel
  have hmoment : injectiveMoment H node2564 = injectiveMoment H pivotMatrix2564 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2564 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2564 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2564 (0 : Fin 4)) =
      Sparse.eval value1298 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2564 (0 : Fin 4) = raw7138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2564 raw7138; decide +kernel
    rw [heq]
    exact (canonical7138 hH).trans (sound1298 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2564 (1 : Fin 4)) =
      Sparse.eval value1064 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2564 (1 : Fin 4) = raw6379 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2564 raw6379; decide +kernel
    rw [heq]
    exact (canonical6379 hH).trans (sound1064 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2564 (2 : Fin 4)) =
      Sparse.eval value1082 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2564 (2 : Fin 4) = raw6355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2564 raw6355; decide +kernel
    rw [heq]
    exact (canonical6355 hH).trans (sound1082 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2564 (3 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2564 (3 : Fin 4) = raw6353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2564 raw6353; decide +kernel
    rw [heq]
    exact (canonical6353 hH).trans (sound1113 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2564 + (injectiveMoment H (mergeFirst pivotMatrix2564 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2564 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2564 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2564 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2564, value1064, value1082, value1113, value1298, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2565 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2565 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

theorem sound2565 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2565 = Sparse.eval value2565 (momentVector H) := by
  have heq : pivotMatrix2565 = (fun u v => node2565 (pivotPermutation2565 u) v) := by apply Matrix.ext; unfold pivotMatrix2565 node2565 pivotPermutation2565; decide +kernel
  have hmoment : injectiveMoment H node2565 = injectiveMoment H pivotMatrix2565 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2565 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2565 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2565 (0 : Fin 4)) =
      Sparse.eval value1367 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2565 (0 : Fin 4) = raw7139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2565 raw7139; decide +kernel
    rw [heq]
    exact (canonical7139 hH).trans (sound1367 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2565 (1 : Fin 4)) =
      Sparse.eval value1342 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2565 (1 : Fin 4) = raw6380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2565 raw6380; decide +kernel
    rw [heq]
    exact (canonical6380 hH).trans (sound1342 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2565 (2 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2565 (2 : Fin 4) = raw6356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2565 raw6356; decide +kernel
    rw [heq]
    exact (canonical6356 hH).trans (sound1083 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2565 (3 : Fin 4)) =
      Sparse.eval value677 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2565 (3 : Fin 4) = raw6354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2565 raw6354; decide +kernel
    rw [heq]
    exact (canonical6354 hH).trans (sound677 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2565 + (injectiveMoment H (mergeFirst pivotMatrix2565 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2565 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2565 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2565 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2565, value1083, value1342, value1367, value677, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2566 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2566 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound2566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2566 = Sparse.eval value2566 (momentVector H) := by
  have heq : pivotMatrix2566 = (fun u v => node2566 (pivotPermutation2566 u) v) := by apply Matrix.ext; unfold pivotMatrix2566 node2566 pivotPermutation2566; decide +kernel
  have hmoment : injectiveMoment H node2566 = injectiveMoment H pivotMatrix2566 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2566 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2566 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2566 (0 : Fin 4)) =
      Sparse.eval value1217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2566 (0 : Fin 4) = raw7274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2566 raw7274; decide +kernel
    rw [heq]
    exact (canonical7274 hH).trans (sound1217 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2566 (1 : Fin 4)) =
      Sparse.eval value1209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2566 (1 : Fin 4) = raw6382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2566 raw6382; decide +kernel
    rw [heq]
    exact (canonical6382 hH).trans (sound1209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2566 (2 : Fin 4)) =
      Sparse.eval value1082 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2566 (2 : Fin 4) = raw6357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2566 raw6357; decide +kernel
    rw [heq]
    exact (canonical6357 hH).trans (sound1082 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2566 (3 : Fin 4)) =
      Sparse.eval value677 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2566 (3 : Fin 4) = raw6354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2566 raw6354; decide +kernel
    rw [heq]
    exact (canonical6354 hH).trans (sound677 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2566 + (injectiveMoment H (mergeFirst pivotMatrix2566 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2566 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2566 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2566 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2566, value1082, value1209, value1217, value677, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2567 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2567 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2567 = Sparse.eval value2567 (momentVector H) := by
  have heq : pivotMatrix2567 = (fun u v => node2567 (pivotPermutation2567 u) v) := by apply Matrix.ext; unfold pivotMatrix2567 node2567 pivotPermutation2567; decide +kernel
  have hmoment : injectiveMoment H node2567 = injectiveMoment H pivotMatrix2567 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2567 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2567 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2567 (0 : Fin 4)) =
      Sparse.eval value1189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2567 (0 : Fin 4) = raw8062 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2567 raw8062; decide +kernel
    rw [heq]
    exact (canonical8062 hH).trans (sound1189 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2567 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2567 (1 : Fin 4) = raw6432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2567 raw6432; decide +kernel
    rw [heq]
    exact (canonical6432 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2567 (2 : Fin 4)) =
      Sparse.eval value1082 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2567 (2 : Fin 4) = raw6357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2567 raw6357; decide +kernel
    rw [heq]
    exact (canonical6357 hH).trans (sound1082 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2567 (3 : Fin 4)) =
      Sparse.eval value583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2567 (3 : Fin 4) = raw6352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2567 raw6352; decide +kernel
    rw [heq]
    exact (canonical6352 hH).trans (sound583 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2567 + (injectiveMoment H (mergeFirst pivotMatrix2567 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2567 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2567 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2567 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2567, value1031, value1082, value1189, value583, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2568 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2568 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem sound2568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2568 = Sparse.eval value2568 (momentVector H) := by
  have heq : pivotMatrix2568 = (fun u v => node2568 (pivotPermutation2568 u) v) := by apply Matrix.ext; unfold pivotMatrix2568 node2568 pivotPermutation2568; decide +kernel
  have hmoment : injectiveMoment H node2568 = injectiveMoment H pivotMatrix2568 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2568 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2568 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2568 (0 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2568 (0 : Fin 4) = raw8063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2568 raw8063; decide +kernel
    rw [heq]
    exact (canonical8063 hH).trans (sound1173 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2568 (1 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2568 (1 : Fin 4) = raw6453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2568 raw6453; decide +kernel
    rw [heq]
    exact (canonical6453 hH).trans (sound1042 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2568 (2 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2568 (2 : Fin 4) = raw6373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2568 raw6373; decide +kernel
    rw [heq]
    exact (canonical6373 hH).trans (sound1080 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2568 (3 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2568 (3 : Fin 4) = raw6360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2568 raw6360; decide +kernel
    rw [heq]
    exact (canonical6360 hH).trans (sound466 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2568 + (injectiveMoment H (mergeFirst pivotMatrix2568 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2568 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2568 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2568 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2568, value1042, value1080, value1173, value466, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2569 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2569 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

theorem sound2569 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2569 = Sparse.eval value2569 (momentVector H) := by
  have heq : pivotMatrix2569 = (fun u v => node2569 (pivotPermutation2569 u) v) := by apply Matrix.ext; unfold pivotMatrix2569 node2569 pivotPermutation2569; decide +kernel
  have hmoment : injectiveMoment H node2569 = injectiveMoment H pivotMatrix2569 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2569 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2569 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2569 (0 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2569 (0 : Fin 4) = raw8375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2569 raw8375; decide +kernel
    rw [heq]
    exact (canonical8375 hH).trans (sound972 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2569 (1 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2569 (1 : Fin 4) = raw6534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2569 raw6534; decide +kernel
    rw [heq]
    exact (canonical6534 hH).trans (sound797 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2569 (2 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2569 (2 : Fin 4) = raw6376 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2569 raw6376; decide +kernel
    rw [heq]
    exact (canonical6376 hH).trans (sound491 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2569 (3 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2569 (3 : Fin 4) = raw6360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2569 raw6360; decide +kernel
    rw [heq]
    exact (canonical6360 hH).trans (sound466 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2569 + (injectiveMoment H (mergeFirst pivotMatrix2569 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2569 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2569 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2569 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2569, value466, value491, value797, value972, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2570 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2570 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem sound2570 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2570 = Sparse.eval value2570 (momentVector H) := by
  have heq : pivotMatrix2570 = (fun u v => node2570 (pivotPermutation2570 u) v) := by apply Matrix.ext; unfold pivotMatrix2570 node2570 pivotPermutation2570; decide +kernel
  have hmoment : injectiveMoment H node2570 = injectiveMoment H pivotMatrix2570 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2570 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2570 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2570 (0 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2570 (0 : Fin 4) = raw7140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2570 raw7140; decide +kernel
    rw [heq]
    exact (canonical7140 hH).trans (sound1341 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2570 (1 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2570 (1 : Fin 4) = raw6381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2570 raw6381; decide +kernel
    rw [heq]
    exact (canonical6381 hH).trans (sound467 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2570 (2 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2570 (2 : Fin 4) = raw6373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2570 raw6373; decide +kernel
    rw [heq]
    exact (canonical6373 hH).trans (sound1080 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2570 (3 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2570 (3 : Fin 4) = raw6371 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2570 raw6371; decide +kernel
    rw [heq]
    exact (canonical6371 hH).trans (sound464 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2570 + (injectiveMoment H (mergeFirst pivotMatrix2570 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2570 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2570 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2570 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2570, value1080, value1341, value464, value467, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2571 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2571 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound2571 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2571 = Sparse.eval value2571 (momentVector H) := by
  have heq : pivotMatrix2571 = (fun u v => node2571 (pivotPermutation2571 u) v) := by apply Matrix.ext; unfold pivotMatrix2571 node2571 pivotPermutation2571; decide +kernel
  have hmoment : injectiveMoment H node2571 = injectiveMoment H pivotMatrix2571 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2571 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2571 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2571 (0 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2571 (0 : Fin 4) = raw7142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2571 raw7142; decide +kernel
    rw [heq]
    exact (canonical7142 hH).trans (sound972 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2571 (1 : Fin 4)) =
      Sparse.eval value1209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2571 (1 : Fin 4) = raw6382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2571 raw6382; decide +kernel
    rw [heq]
    exact (canonical6382 hH).trans (sound1209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2571 (2 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2571 (2 : Fin 4) = raw6374 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2571 raw6374; decide +kernel
    rw [heq]
    exact (canonical6374 hH).trans (sound1081 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2571 (3 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2571 (3 : Fin 4) = raw6372 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2571 raw6372; decide +kernel
    rw [heq]
    exact (canonical6372 hH).trans (sound491 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2571 + (injectiveMoment H (mergeFirst pivotMatrix2571 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2571 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2571 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2571 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2571, value1081, value1209, value491, value972, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2572 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2572 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

theorem sound2572 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2572 = Sparse.eval value2572 (momentVector H) := by
  have heq : pivotMatrix2572 = (fun u v => node2572 (pivotPermutation2572 u) v) := by apply Matrix.ext; unfold pivotMatrix2572 node2572 pivotPermutation2572; decide +kernel
  have hmoment : injectiveMoment H node2572 = injectiveMoment H pivotMatrix2572 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2572 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2572 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2572 (0 : Fin 4)) =
      Sparse.eval value933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2572 (0 : Fin 4) = raw7275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2572 raw7275; decide +kernel
    rw [heq]
    exact (canonical7275 hH).trans (sound933 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2572 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2572 (1 : Fin 4) = raw6383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2572 raw6383; decide +kernel
    rw [heq]
    exact (canonical6383 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2572 (2 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2572 (2 : Fin 4) = raw6375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2572 raw6375; decide +kernel
    rw [heq]
    exact (canonical6375 hH).trans (sound1080 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2572 (3 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2572 (3 : Fin 4) = raw6372 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2572 raw6372; decide +kernel
    rw [heq]
    exact (canonical6372 hH).trans (sound491 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2572 + (injectiveMoment H (mergeFirst pivotMatrix2572 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2572 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2572 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2572 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2572, value1080, value491, value495, value933, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2573 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2573 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem sound2573 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2573 = Sparse.eval value2573 (momentVector H) := by
  have heq : pivotMatrix2573 = (fun u v => node2573 (pivotPermutation2573 u) v) := by apply Matrix.ext; unfold pivotMatrix2573 node2573 pivotPermutation2573; decide +kernel
  have hmoment : injectiveMoment H node2573 = injectiveMoment H pivotMatrix2573 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2573 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2573 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2573 (0 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2573 (0 : Fin 4) = raw8065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2573 raw8065; decide +kernel
    rw [heq]
    exact (canonical8065 hH).trans (sound1306 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2573 (1 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2573 (1 : Fin 4) = raw6468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2573 raw6468; decide +kernel
    rw [heq]
    exact (canonical6468 hH).trans (sound1042 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2573 (2 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2573 (2 : Fin 4) = raw6375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2573 raw6375; decide +kernel
    rw [heq]
    exact (canonical6375 hH).trans (sound1080 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2573 (3 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2573 (3 : Fin 4) = raw6370 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2573 raw6370; decide +kernel
    rw [heq]
    exact (canonical6370 hH).trans (sound467 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2573 + (injectiveMoment H (mergeFirst pivotMatrix2573 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2573 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2573 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2573 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2573, value1042, value1080, value1306, value467, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2574 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2574 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound2574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2574 = Sparse.eval value2574 (momentVector H) := by
  have heq : pivotMatrix2574 = (fun u v => node2574 (pivotPermutation2574 u) v) := by apply Matrix.ext; unfold pivotMatrix2574 node2574 pivotPermutation2574; decide +kernel
  have hmoment : injectiveMoment H node2574 = injectiveMoment H pivotMatrix2574 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2574 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2574 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2574 (0 : Fin 4)) =
      Sparse.eval value1197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2574 (0 : Fin 4) = raw7284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2574 raw7284; decide +kernel
    rw [heq]
    exact (canonical7284 hH).trans (sound1197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2574 (1 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2574 (1 : Fin 4) = raw6431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2574 raw6431; decide +kernel
    rw [heq]
    exact (canonical6431 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2574 (2 : Fin 4)) =
      Sparse.eval value994 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2574 (2 : Fin 4) = raw6385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2574 raw6385; decide +kernel
    rw [heq]
    exact (canonical6385 hH).trans (sound994 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2574 (3 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2574 (3 : Fin 4) = raw6384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2574 raw6384; decide +kernel
    rw [heq]
    exact (canonical6384 hH).trans (sound991 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2574 + (injectiveMoment H (mergeFirst pivotMatrix2574 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2574 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2574 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2574 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2574, value1032, value1197, value991, value994, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2575 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2575 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem sound2575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2575 = Sparse.eval value2575 (momentVector H) := by
  have heq : pivotMatrix2575 = (fun u v => node2575 (pivotPermutation2575 u) v) := by apply Matrix.ext; unfold pivotMatrix2575 node2575 pivotPermutation2575; decide +kernel
  have hmoment : injectiveMoment H node2575 = injectiveMoment H pivotMatrix2575 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2575 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2575 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2575 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2575 (0 : Fin 4) = raw7167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2575 raw7167; decide +kernel
    rw [heq]
    exact (canonical7167 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2575 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2575 (1 : Fin 4) = raw6427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2575 raw6427; decide +kernel
    rw [heq]
    exact (canonical6427 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2575 (2 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2575 (2 : Fin 4) = raw6393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2575 raw6393; decide +kernel
    rw [heq]
    exact (canonical6393 hH).trans (sound997 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2575 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2575 (3 : Fin 4) = raw6390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2575 raw6390; decide +kernel
    rw [heq]
    exact (canonical6390 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2575 + (injectiveMoment H (mergeFirst pivotMatrix2575 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2575 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2575 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2575 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2575, value1031, value1168, value786, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2576 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2576 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound2576 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2576 = Sparse.eval value2576 (momentVector H) := by
  have heq : pivotMatrix2576 = (fun u v => node2576 (pivotPermutation2576 u) v) := by apply Matrix.ext; unfold pivotMatrix2576 node2576 pivotPermutation2576; decide +kernel
  have hmoment : injectiveMoment H node2576 = injectiveMoment H pivotMatrix2576 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2576 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2576 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2576 (0 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2576 (0 : Fin 4) = raw7168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2576 raw7168; decide +kernel
    rw [heq]
    exact (canonical7168 hH).trans (sound1198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2576 (1 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2576 (1 : Fin 4) = raw6431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2576 raw6431; decide +kernel
    rw [heq]
    exact (canonical6431 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2576 (2 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2576 (2 : Fin 4) = raw6395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2576 raw6395; decide +kernel
    rw [heq]
    exact (canonical6395 hH).trans (sound1198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2576 (3 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2576 (3 : Fin 4) = raw6391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2576 raw6391; decide +kernel
    rw [heq]
    exact (canonical6391 hH).trans (sound995 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2576 + (injectiveMoment H (mergeFirst pivotMatrix2576 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2576 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2576 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2576 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2576, value1032, value1198, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2577 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2577 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2577 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2577 = Sparse.eval value2577 (momentVector H) := by
  have heq : pivotMatrix2577 = (fun u v => node2577 (pivotPermutation2577 u) v) := by apply Matrix.ext; unfold pivotMatrix2577 node2577 pivotPermutation2577; decide +kernel
  have hmoment : injectiveMoment H node2577 = injectiveMoment H pivotMatrix2577 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2577 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2577 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2577 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2577 (0 : Fin 4) = raw7169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2577 raw7169; decide +kernel
    rw [heq]
    exact (canonical7169 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2577 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2577 (1 : Fin 4) = raw6432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2577 raw6432; decide +kernel
    rw [heq]
    exact (canonical6432 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2577 (2 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2577 (2 : Fin 4) = raw6396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2577 raw6396; decide +kernel
    rw [heq]
    exact (canonical6396 hH).trans (sound998 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2577 (3 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2577 (3 : Fin 4) = raw6392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2577 raw6392; decide +kernel
    rw [heq]
    exact (canonical6392 hH).trans (sound996 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2577 + (injectiveMoment H (mergeFirst pivotMatrix2577 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2577 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2577 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2577 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2577, value1031, value1168, value996, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2578 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2578 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2578 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2578 = Sparse.eval value2578 (momentVector H) := by
  have heq : pivotMatrix2578 = (fun u v => node2578 (pivotPermutation2578 u) v) := by apply Matrix.ext; unfold pivotMatrix2578 node2578 pivotPermutation2578; decide +kernel
  have hmoment : injectiveMoment H node2578 = injectiveMoment H pivotMatrix2578 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2578 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2578 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2578 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2578 (0 : Fin 4) = raw5663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2578 raw5663; decide +kernel
    rw [heq]
    exact (canonical5663 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2578 (1 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2578 (1 : Fin 4) = raw6396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2578 raw6396; decide +kernel
    rw [heq]
    exact (canonical6396 hH).trans (sound998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2578 (2 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2578 (2 : Fin 4) = raw6467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2578 raw6467; decide +kernel
    rw [heq]
    exact (canonical6467 hH).trans (sound1043 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2578 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2578 (3 : Fin 4) = raw6472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2578 raw6472; decide +kernel
    rw [heq]
    exact (canonical6472 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2578 + (injectiveMoment H (mergeFirst pivotMatrix2578 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2578 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2578 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2578 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2578, value1031, value1043, value786, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2579 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2579 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2579 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2579 = Sparse.eval value2579 (momentVector H) := by
  have heq : pivotMatrix2579 = (fun u v => node2579 (pivotPermutation2579 u) v) := by apply Matrix.ext; unfold pivotMatrix2579 node2579 pivotPermutation2579; decide +kernel
  have hmoment : injectiveMoment H node2579 = injectiveMoment H pivotMatrix2579 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2579 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2579 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2579 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2579 (0 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2579 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2579 (1 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2579 (1 : Fin 4) = raw6467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2579 raw6467; decide +kernel
    rw [heq]
    exact (canonical6467 hH).trans (sound1043 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2579 (2 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2579 (2 : Fin 4) = raw6533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2579 raw6533; decide +kernel
    rw [heq]
    exact (canonical6533 hH).trans (sound1054 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2579 (3 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2579 (3 : Fin 4) = raw6538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2579 raw6538; decide +kernel
    rw [heq]
    exact (canonical6538 hH).trans (sound1081 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2579 + (injectiveMoment H (mergeFirst pivotMatrix2579 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2579 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2579 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2579 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2579, value1043, value1054, value1063, value1081, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2580 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2580 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2580 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2580 = Sparse.eval value2580 (momentVector H) := by
  have heq : pivotMatrix2580 = (fun u v => node2580 (pivotPermutation2580 u) v) := by apply Matrix.ext; unfold pivotMatrix2580 node2580 pivotPermutation2580; decide +kernel
  have hmoment : injectiveMoment H node2580 = injectiveMoment H pivotMatrix2580 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2580 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2580 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2580 (0 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2580 (0 : Fin 4) = raw5755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2580 raw5755; decide +kernel
    rw [heq]
    exact (canonical5755 hH).trans (sound1109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2580 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2580 (1 : Fin 4) = raw6401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2580 raw6401; decide +kernel
    rw [heq]
    exact (canonical6401 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2580 (2 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2580 (2 : Fin 4) = raw6467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2580 raw6467; decide +kernel
    rw [heq]
    exact (canonical6467 hH).trans (sound1043 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2580 (3 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2580 (3 : Fin 4) = raw6471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2580 raw6471; decide +kernel
    rw [heq]
    exact (canonical6471 hH).trans (sound1203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2580 + (injectiveMoment H (mergeFirst pivotMatrix2580 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2580 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2580 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2580 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2580, value1043, value1109, value1202, value1203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2581 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2581 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem sound2581 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2581 = Sparse.eval value2581 (momentVector H) := by
  have heq : pivotMatrix2581 = (fun u v => node2581 (pivotPermutation2581 u) v) := by apply Matrix.ext; unfold pivotMatrix2581 node2581 pivotPermutation2581; decide +kernel
  have hmoment : injectiveMoment H node2581 = injectiveMoment H pivotMatrix2581 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2581 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2581 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2581 (0 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2581 (0 : Fin 4) = raw5765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2581 raw5765; decide +kernel
    rw [heq]
    exact (canonical5765 hH).trans (sound1260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2581 (1 : Fin 4)) =
      Sparse.eval value1006 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2581 (1 : Fin 4) = raw6411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2581 raw6411; decide +kernel
    rw [heq]
    exact (canonical6411 hH).trans (sound1006 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2581 (2 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2581 (2 : Fin 4) = raw6477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2581 raw6477; decide +kernel
    rw [heq]
    exact (canonical6477 hH).trans (sound287 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2581 (3 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2581 (3 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2581 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2581 + (injectiveMoment H (mergeFirst pivotMatrix2581 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2581 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2581 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2581 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2581, value1006, value1048, value1260, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2582 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2582 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem sound2582 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2582 = Sparse.eval value2582 (momentVector H) := by
  have heq : pivotMatrix2582 = (fun u v => node2582 (pivotPermutation2582 u) v) := by apply Matrix.ext; unfold pivotMatrix2582 node2582 pivotPermutation2582; decide +kernel
  have hmoment : injectiveMoment H node2582 = injectiveMoment H pivotMatrix2582 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2582 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2582 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2582 (0 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2582 (0 : Fin 4) = raw5766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2582 raw5766; decide +kernel
    rw [heq]
    exact (canonical5766 hH).trans (sound1047 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2582 (1 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2582 (1 : Fin 4) = raw6412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2582 raw6412; decide +kernel
    rw [heq]
    exact (canonical6412 hH).trans (sound1000 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2582 (2 : Fin 4)) =
      Sparse.eval value1045 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2582 (2 : Fin 4) = raw6481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2582 raw6481; decide +kernel
    rw [heq]
    exact (canonical6481 hH).trans (sound1045 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2582 (3 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2582 (3 : Fin 4) = raw6488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2582 raw6488; decide +kernel
    rw [heq]
    exact (canonical6488 hH).trans (sound1048 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2582 + (injectiveMoment H (mergeFirst pivotMatrix2582 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2582 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2582 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2582 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2582, value1000, value1045, value1047, value1048, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2583 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2583 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound2583 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2583 = Sparse.eval value2583 (momentVector H) := by
  have heq : pivotMatrix2583 = (fun u v => node2583 (pivotPermutation2583 u) v) := by apply Matrix.ext; unfold pivotMatrix2583 node2583 pivotPermutation2583; decide +kernel
  have hmoment : injectiveMoment H node2583 = injectiveMoment H pivotMatrix2583 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2583 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2583 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2583 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2583 (0 : Fin 4) = raw5768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2583 raw5768; decide +kernel
    rw [heq]
    exact (canonical5768 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2583 (1 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2583 (1 : Fin 4) = raw6414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2583 raw6414; decide +kernel
    rw [heq]
    exact (canonical6414 hH).trans (sound1008 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2583 (2 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2583 (2 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2583 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2583 (3 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2583 (3 : Fin 4) = raw6490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2583 raw6490; decide +kernel
    rw [heq]
    exact (canonical6490 hH).trans (sound1000 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2583 + (injectiveMoment H (mergeFirst pivotMatrix2583 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2583 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2583 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2583 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2583, value1000, value1008, value1048, value1053, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2584 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2584 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound2584 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2584 = Sparse.eval value2584 (momentVector H) := by
  have heq : pivotMatrix2584 = (fun u v => node2584 (pivotPermutation2584 u) v) := by apply Matrix.ext; unfold pivotMatrix2584 node2584 pivotPermutation2584; decide +kernel
  have hmoment : injectiveMoment H node2584 = injectiveMoment H pivotMatrix2584 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2584 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2584 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2584 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2584 (0 : Fin 4) = raw5769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2584 raw5769; decide +kernel
    rw [heq]
    exact (canonical5769 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2584 (1 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2584 (1 : Fin 4) = raw6415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2584 raw6415; decide +kernel
    rw [heq]
    exact (canonical6415 hH).trans (sound1009 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2584 (2 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2584 (2 : Fin 4) = raw6488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2584 raw6488; decide +kernel
    rw [heq]
    exact (canonical6488 hH).trans (sound1048 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2584 (3 : Fin 4)) =
      Sparse.eval value1246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2584 (3 : Fin 4) = raw6491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2584 raw6491; decide +kernel
    rw [heq]
    exact (canonical6491 hH).trans (sound1246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2584 + (injectiveMoment H (mergeFirst pivotMatrix2584 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2584 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2584 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2584 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2584, value1009, value1048, value1246, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2585 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2585 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2585 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2585 = Sparse.eval value2585 (momentVector H) := by
  have heq : pivotMatrix2585 = (fun u v => node2585 (pivotPermutation2585 u) v) := by apply Matrix.ext; unfold pivotMatrix2585 node2585 pivotPermutation2585; decide +kernel
  have hmoment : injectiveMoment H node2585 = injectiveMoment H pivotMatrix2585 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2585 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2585 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2585 (0 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2585 (0 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2585 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2585 (1 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2585 (1 : Fin 4) = raw6466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2585 raw6466; decide +kernel
    rw [heq]
    exact (canonical6466 hH).trans (sound1044 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2585 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2585 (2 : Fin 4) = raw6526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2585 raw6526; decide +kernel
    rw [heq]
    exact (canonical6526 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2585 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2585 (3 : Fin 4) = raw6529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2585 raw6529; decide +kernel
    rw [heq]
    exact (canonical6529 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2585 + (injectiveMoment H (mergeFirst pivotMatrix2585 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2585 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2585 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2585 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2585, value1044, value1053, value1078, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2586 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2586 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2586 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2586 = Sparse.eval value2586 (momentVector H) := by
  have heq : pivotMatrix2586 = (fun u v => node2586 (pivotPermutation2586 u) v) := by apply Matrix.ext; unfold pivotMatrix2586 node2586 pivotPermutation2586; decide +kernel
  have hmoment : injectiveMoment H node2586 = injectiveMoment H pivotMatrix2586 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2586 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2586 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2586 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2586 (0 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2586 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2586 (1 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2586 (1 : Fin 4) = raw6473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2586 raw6473; decide +kernel
    rw [heq]
    exact (canonical6473 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2586 (2 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2586 (2 : Fin 4) = raw6533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2586 raw6533; decide +kernel
    rw [heq]
    exact (canonical6533 hH).trans (sound1054 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2586 (3 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2586 (3 : Fin 4) = raw6537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2586 raw6537; decide +kernel
    rw [heq]
    exact (canonical6537 hH).trans (sound1242 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2586 + (injectiveMoment H (mergeFirst pivotMatrix2586 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2586 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2586 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2586 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2586, value1054, value1110, value1242, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2587 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2587 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2587 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2587 = Sparse.eval value2587 (momentVector H) := by
  have heq : pivotMatrix2587 = (fun u v => node2587 (pivotPermutation2587 u) v) := by apply Matrix.ext; unfold pivotMatrix2587 node2587 pivotPermutation2587; decide +kernel
  have hmoment : injectiveMoment H node2587 = injectiveMoment H pivotMatrix2587 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2587 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2587 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2587 (0 : Fin 4)) =
      Sparse.eval value1245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2587 (0 : Fin 4) = raw7177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2587 raw7177; decide +kernel
    rw [heq]
    exact (canonical7177 hH).trans (sound1245 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2587 (1 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2587 (1 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2587 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2587 (2 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2587 (2 : Fin 4) = raw6414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2587 raw6414; decide +kernel
    rw [heq]
    exact (canonical6414 hH).trans (sound1008 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2587 (3 : Fin 4)) =
      Sparse.eval value1006 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2587 (3 : Fin 4) = raw6411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2587 raw6411; decide +kernel
    rw [heq]
    exact (canonical6411 hH).trans (sound1006 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2587 + (injectiveMoment H (mergeFirst pivotMatrix2587 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2587 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2587 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2587 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2587, value1006, value1008, value1048, value1245, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2588 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2588 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2588 = Sparse.eval value2588 (momentVector H) := by
  have heq : pivotMatrix2588 = (fun u v => node2588 (pivotPermutation2588 u) v) := by apply Matrix.ext; unfold pivotMatrix2588 node2588 pivotPermutation2588; decide +kernel
  have hmoment : injectiveMoment H node2588 = injectiveMoment H pivotMatrix2588 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2588 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2588 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2588 (0 : Fin 4)) =
      Sparse.eval value1246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2588 (0 : Fin 4) = raw7178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2588 raw7178; decide +kernel
    rw [heq]
    exact (canonical7178 hH).trans (sound1246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2588 (1 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2588 (1 : Fin 4) = raw6488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2588 raw6488; decide +kernel
    rw [heq]
    exact (canonical6488 hH).trans (sound1048 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2588 (2 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2588 (2 : Fin 4) = raw6415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2588 raw6415; decide +kernel
    rw [heq]
    exact (canonical6415 hH).trans (sound1009 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2588 (3 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2588 (3 : Fin 4) = raw6412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2588 raw6412; decide +kernel
    rw [heq]
    exact (canonical6412 hH).trans (sound1000 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2588 + (injectiveMoment H (mergeFirst pivotMatrix2588 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2588 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2588 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2588 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2588, value1000, value1009, value1048, value1246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2589 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2589 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem sound2589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2589 = Sparse.eval value2589 (momentVector H) := by
  have heq : pivotMatrix2589 = (fun u v => node2589 (pivotPermutation2589 u) v) := by apply Matrix.ext; unfold pivotMatrix2589 node2589 pivotPermutation2589; decide +kernel
  have hmoment : injectiveMoment H node2589 = injectiveMoment H pivotMatrix2589 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2589 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2589 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2589 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2589 (0 : Fin 4) = raw6638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2589 raw6638; decide +kernel
    rw [heq]
    exact (canonical6638 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2589 (1 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2589 (1 : Fin 4) = raw6471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2589 raw6471; decide +kernel
    rw [heq]
    exact (canonical6471 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2589 (2 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2589 (2 : Fin 4) = raw6436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2589 raw6436; decide +kernel
    rw [heq]
    exact (canonical6436 hH).trans (sound1037 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2589 (3 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2589 (3 : Fin 4) = raw6435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2589 raw6435; decide +kernel
    rw [heq]
    exact (canonical6435 hH).trans (sound1036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2589 + (injectiveMoment H (mergeFirst pivotMatrix2589 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2589 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2589 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2589 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2589, value1036, value1037, value1079, value1203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2590 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2590 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

theorem sound2590 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2590 = Sparse.eval value2590 (momentVector H) := by
  have heq : pivotMatrix2590 = (fun u v => node2590 (pivotPermutation2590 u) v) := by apply Matrix.ext; unfold pivotMatrix2590 node2590 pivotPermutation2590; decide +kernel
  have hmoment : injectiveMoment H node2590 = injectiveMoment H pivotMatrix2590 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2590 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2590 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2590 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2590 (0 : Fin 4) = raw7187 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2590 raw7187; decide +kernel
    rw [heq]
    exact (canonical7187 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2590 (1 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2590 (1 : Fin 4) = raw6521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2590 raw6521; decide +kernel
    rw [heq]
    exact (canonical6521 hH).trans (sound1062 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2590 (2 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2590 (2 : Fin 4) = raw6431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2590 raw6431; decide +kernel
    rw [heq]
    exact (canonical6431 hH).trans (sound1032 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2590 (3 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2590 (3 : Fin 4) = raw6423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2590 raw6423; decide +kernel
    rw [heq]
    exact (canonical6423 hH).trans (sound1028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2590 + (injectiveMoment H (mergeFirst pivotMatrix2590 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2590 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2590 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2590 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2590, value1028, value1032, value1062, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2591 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2591 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem sound2591 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2591 = Sparse.eval value2591 (momentVector H) := by
  have heq : pivotMatrix2591 = (fun u v => node2591 (pivotPermutation2591 u) v) := by apply Matrix.ext; unfold pivotMatrix2591 node2591 pivotPermutation2591; decide +kernel
  have hmoment : injectiveMoment H node2591 = injectiveMoment H pivotMatrix2591 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2591 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2591 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2591 (0 : Fin 4)) =
      Sparse.eval value1252 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2591 (0 : Fin 4) = raw7188 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2591 raw7188; decide +kernel
    rw [heq]
    exact (canonical7188 hH).trans (sound1252 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2591 (1 : Fin 4)) =
      Sparse.eval value1072 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2591 (1 : Fin 4) = raw6522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2591 raw6522; decide +kernel
    rw [heq]
    exact (canonical6522 hH).trans (sound1072 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2591 (2 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2591 (2 : Fin 4) = raw6433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2591 raw6433; decide +kernel
    rw [heq]
    exact (canonical6433 hH).trans (sound1035 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2591 (3 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2591 (3 : Fin 4) = raw6430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2591 raw6430; decide +kernel
    rw [heq]
    exact (canonical6430 hH).trans (sound1032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2591 + (injectiveMoment H (mergeFirst pivotMatrix2591 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2591 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2591 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2591 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2591, value1032, value1035, value1072, value1252, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2592 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2592 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2592 = Sparse.eval value2592 (momentVector H) := by
  have heq : pivotMatrix2592 = (fun u v => node2592 (pivotPermutation2592 u) v) := by apply Matrix.ext; unfold pivotMatrix2592 node2592 pivotPermutation2592; decide +kernel
  have hmoment : injectiveMoment H node2592 = injectiveMoment H pivotMatrix2592 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2592 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2592 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2592 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2592 (0 : Fin 4) = raw7189 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2592 raw7189; decide +kernel
    rw [heq]
    exact (canonical7189 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2592 (1 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2592 (1 : Fin 4) = raw6524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2592 raw6524; decide +kernel
    rw [heq]
    exact (canonical6524 hH).trans (sound1075 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2592 (2 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2592 (2 : Fin 4) = raw6436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2592 raw6436; decide +kernel
    rw [heq]
    exact (canonical6436 hH).trans (sound1037 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2592 (3 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2592 (3 : Fin 4) = raw6432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2592 raw6432; decide +kernel
    rw [heq]
    exact (canonical6432 hH).trans (sound1031 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2592 + (injectiveMoment H (mergeFirst pivotMatrix2592 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2592 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2592 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2592 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2592, value1031, value1037, value1075, value1178, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2593 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2593 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem sound2593 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2593 = Sparse.eval value2593 (momentVector H) := by
  have heq : pivotMatrix2593 = (fun u v => node2593 (pivotPermutation2593 u) v) := by apply Matrix.ext; unfold pivotMatrix2593 node2593 pivotPermutation2593; decide +kernel
  have hmoment : injectiveMoment H node2593 = injectiveMoment H pivotMatrix2593 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2593 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2593 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2593 (0 : Fin 4)) =
      Sparse.eval value962 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2593 (0 : Fin 4) = raw6238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2593 raw6238; decide +kernel
    rw [heq]
    exact (canonical6238 hH).trans (sound962 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2593 (1 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2593 (1 : Fin 4) = raw6427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2593 raw6427; decide +kernel
    rw [heq]
    exact (canonical6427 hH).trans (sound1031 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2593 (2 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2593 (2 : Fin 4) = raw6453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2593 raw6453; decide +kernel
    rw [heq]
    exact (canonical6453 hH).trans (sound1042 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2593 (3 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2593 (3 : Fin 4) = raw6462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2593 raw6462; decide +kernel
    rw [heq]
    exact (canonical6462 hH).trans (sound1043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2593 + (injectiveMoment H (mergeFirst pivotMatrix2593 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2593 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2593 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2593 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2593, value1031, value1042, value1043, value962, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2594 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2594 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem sound2594 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2594 = Sparse.eval value2594 (momentVector H) := by
  have heq : pivotMatrix2594 = (fun u v => node2594 (pivotPermutation2594 u) v) := by apply Matrix.ext; unfold pivotMatrix2594 node2594 pivotPermutation2594; decide +kernel
  have hmoment : injectiveMoment H node2594 = injectiveMoment H pivotMatrix2594 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2594 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2594 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2594 (0 : Fin 4)) =
      Sparse.eval value963 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2594 (0 : Fin 4) = raw6241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2594 raw6241; decide +kernel
    rw [heq]
    exact (canonical6241 hH).trans (sound963 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2594 (1 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2594 (1 : Fin 4) = raw6430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2594 raw6430; decide +kernel
    rw [heq]
    exact (canonical6430 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2594 (2 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2594 (2 : Fin 4) = raw6462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2594 raw6462; decide +kernel
    rw [heq]
    exact (canonical6462 hH).trans (sound1043 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2594 (3 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2594 (3 : Fin 4) = raw6465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2594 raw6465; decide +kernel
    rw [heq]
    exact (canonical6465 hH).trans (sound1044 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2594 + (injectiveMoment H (mergeFirst pivotMatrix2594 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2594 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2594 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2594 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2594, value1032, value1043, value1044, value963, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2595 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2595 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

theorem sound2595 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2595 = Sparse.eval value2595 (momentVector H) := by
  have heq : pivotMatrix2595 = (fun u v => node2595 (pivotPermutation2595 u) v) := by apply Matrix.ext; unfold pivotMatrix2595 node2595 pivotPermutation2595; decide +kernel
  have hmoment : injectiveMoment H node2595 = injectiveMoment H pivotMatrix2595 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2595 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2595 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2595 (0 : Fin 4)) =
      Sparse.eval value933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2595 (0 : Fin 4) = raw6243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2595 raw6243; decide +kernel
    rw [heq]
    exact (canonical6243 hH).trans (sound933 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2595 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2595 (1 : Fin 4) = raw6435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2595 raw6435; decide +kernel
    rw [heq]
    exact (canonical6435 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2595 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2595 (2 : Fin 4) = raw6470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2595 raw6470; decide +kernel
    rw [heq]
    exact (canonical6470 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2595 (3 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2595 (3 : Fin 4) = raw6471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2595 raw6471; decide +kernel
    rw [heq]
    exact (canonical6471 hH).trans (sound1203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2595 + (injectiveMoment H (mergeFirst pivotMatrix2595 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2595 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2595 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2595 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2595, value1036, value1110, value1203, value933, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2596 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2596 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem sound2596 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2596 = Sparse.eval value2596 (momentVector H) := by
  have heq : pivotMatrix2596 = (fun u v => node2596 (pivotPermutation2596 u) v) := by apply Matrix.ext; unfold pivotMatrix2596 node2596 pivotPermutation2596; decide +kernel
  have hmoment : injectiveMoment H node2596 = injectiveMoment H pivotMatrix2596 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2596 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2596 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2596 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2596 (0 : Fin 4) = raw6244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2596 raw6244; decide +kernel
    rw [heq]
    exact (canonical6244 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2596 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2596 (1 : Fin 4) = raw6436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2596 raw6436; decide +kernel
    rw [heq]
    exact (canonical6436 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2596 (2 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2596 (2 : Fin 4) = raw6471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2596 raw6471; decide +kernel
    rw [heq]
    exact (canonical6471 hH).trans (sound1203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2596 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2596 (3 : Fin 4) = raw6472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2596 raw6472; decide +kernel
    rw [heq]
    exact (canonical6472 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2596 + (injectiveMoment H (mergeFirst pivotMatrix2596 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2596 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2596 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2596 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2596, value1037, value1168, value1203, value786, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2597 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2597 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem sound2597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2597 = Sparse.eval value2597 (momentVector H) := by
  have heq : pivotMatrix2597 = (fun u v => node2597 (pivotPermutation2597 u) v) := by apply Matrix.ext; unfold pivotMatrix2597 node2597 pivotPermutation2597; decide +kernel
  have hmoment : injectiveMoment H node2597 = injectiveMoment H pivotMatrix2597 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2597 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2597 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2597 (0 : Fin 4)) =
      Sparse.eval value972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2597 (0 : Fin 4) = raw6282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2597 raw6282; decide +kernel
    rw [heq]
    exact (canonical6282 hH).trans (sound972 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2597 (1 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2597 (1 : Fin 4) = raw6474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2597 raw6474; decide +kernel
    rw [heq]
    exact (canonical6474 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2597 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2597 (2 : Fin 4) = raw6492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2597 raw6492; decide +kernel
    rw [heq]
    exact (canonical6492 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2597 (3 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2597 (3 : Fin 4) = raw6493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2597 raw6493; decide +kernel
    rw [heq]
    exact (canonical6493 hH).trans (sound1050 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2597 + (injectiveMoment H (mergeFirst pivotMatrix2597 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2597 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2597 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2597 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2597, value1050, value1265, value181, value972, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2598 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2598 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2598 = Sparse.eval value2598 (momentVector H) := by
  have heq : pivotMatrix2598 = (fun u v => node2598 (pivotPermutation2598 u) v) := by apply Matrix.ext; unfold pivotMatrix2598 node2598 pivotPermutation2598; decide +kernel
  have hmoment : injectiveMoment H node2598 = injectiveMoment H pivotMatrix2598 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2598 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2598 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2598 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2598 (0 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2598 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2598 (1 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2598 (1 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2598 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2598 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2598 (2 : Fin 4) = raw6498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2598 raw6498; decide +kernel
    rw [heq]
    exact (canonical6498 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2598 (3 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2598 (3 : Fin 4) = raw6503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2598 raw6503; decide +kernel
    rw [heq]
    exact (canonical6503 hH).trans (sound1054 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2598 + (injectiveMoment H (mergeFirst pivotMatrix2598 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2598 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2598 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2598 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2598, value1048, value1053, value1054, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2599 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2599 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2599 = Sparse.eval value2599 (momentVector H) := by
  have heq : pivotMatrix2599 = (fun u v => node2599 (pivotPermutation2599 u) v) := by apply Matrix.ext; unfold pivotMatrix2599 node2599 pivotPermutation2599; decide +kernel
  have hmoment : injectiveMoment H node2599 = injectiveMoment H pivotMatrix2599 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2599 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2599 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2599 (0 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2599 (0 : Fin 4) = raw6293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2599 raw6293; decide +kernel
    rw [heq]
    exact (canonical6293 hH).trans (sound977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2599 (1 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2599 (1 : Fin 4) = raw6498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2599 raw6498; decide +kernel
    rw [heq]
    exact (canonical6498 hH).trans (sound1053 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2599 (2 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2599 (2 : Fin 4) = raw6511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2599 raw6511; decide +kernel
    rw [heq]
    exact (canonical6511 hH).trans (sound1062 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2599 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2599 (3 : Fin 4) = raw6513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2599 raw6513; decide +kernel
    rw [heq]
    exact (canonical6513 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2599 + (injectiveMoment H (mergeFirst pivotMatrix2599 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2599 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2599 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2599 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2599, value1053, value1062, value1063, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2600 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2600 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem sound2600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2600 = Sparse.eval value2600 (momentVector H) := by
  have heq : pivotMatrix2600 = (fun u v => node2600 (pivotPermutation2600 u) v) := by apply Matrix.ext; unfold pivotMatrix2600 node2600 pivotPermutation2600; decide +kernel
  have hmoment : injectiveMoment H node2600 = injectiveMoment H pivotMatrix2600 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2600 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2600 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2600 (0 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2600 (0 : Fin 4) = raw6295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2600 raw6295; decide +kernel
    rw [heq]
    exact (canonical6295 hH).trans (sound978 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2600 (1 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2600 (1 : Fin 4) = raw6503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2600 raw6503; decide +kernel
    rw [heq]
    exact (canonical6503 hH).trans (sound1054 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2600 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2600 (2 : Fin 4) = raw6513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2600 raw6513; decide +kernel
    rw [heq]
    exact (canonical6513 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2600 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2600 (3 : Fin 4) = raw6516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2600 raw6516; decide +kernel
    rw [heq]
    exact (canonical6516 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2600 + (injectiveMoment H (mergeFirst pivotMatrix2600 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2600 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2600 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2600 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2600, value1054, value1063, value978, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2601 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2601 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem sound2601 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2601 = Sparse.eval value2601 (momentVector H) := by
  have heq : pivotMatrix2601 = (fun u v => node2601 (pivotPermutation2601 u) v) := by apply Matrix.ext; unfold pivotMatrix2601 node2601 pivotPermutation2601; decide +kernel
  have hmoment : injectiveMoment H node2601 = injectiveMoment H pivotMatrix2601 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2601 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2601 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2601 (0 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2601 (0 : Fin 4) = raw6297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2601 raw6297; decide +kernel
    rw [heq]
    exact (canonical6297 hH).trans (sound979 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2601 (1 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2601 (1 : Fin 4) = raw6507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2601 raw6507; decide +kernel
    rw [heq]
    exact (canonical6507 hH).trans (sound1057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2601 (2 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2601 (2 : Fin 4) = raw6517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2601 raw6517; decide +kernel
    rw [heq]
    exact (canonical6517 hH).trans (sound1065 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2601 (3 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2601 (3 : Fin 4) = raw6518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2601 raw6518; decide +kernel
    rw [heq]
    exact (canonical6518 hH).trans (sound1066 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2601 + (injectiveMoment H (mergeFirst pivotMatrix2601 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2601 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2601 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2601 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2601, value1057, value1065, value1066, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2602 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2602 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem sound2602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2602 = Sparse.eval value2602 (momentVector H) := by
  have heq : pivotMatrix2602 = (fun u v => node2602 (pivotPermutation2602 u) v) := by apply Matrix.ext; unfold pivotMatrix2602 node2602 pivotPermutation2602; decide +kernel
  have hmoment : injectiveMoment H node2602 = injectiveMoment H pivotMatrix2602 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2602 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2602 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2602 (0 : Fin 4)) =
      Sparse.eval value982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2602 (0 : Fin 4) = raw6300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2602 raw6300; decide +kernel
    rw [heq]
    exact (canonical6300 hH).trans (sound982 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2602 (1 : Fin 4)) =
      Sparse.eval value1072 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2602 (1 : Fin 4) = raw6522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2602 raw6522; decide +kernel
    rw [heq]
    exact (canonical6522 hH).trans (sound1072 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2602 (2 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2602 (2 : Fin 4) = raw6527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2602 raw6527; decide +kernel
    rw [heq]
    exact (canonical6527 hH).trans (sound797 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2602 (3 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2602 (3 : Fin 4) = raw6528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2602 raw6528; decide +kernel
    rw [heq]
    exact (canonical6528 hH).trans (sound837 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2602 + (injectiveMoment H (mergeFirst pivotMatrix2602 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2602 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2602 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2602 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2602, value1072, value797, value837, value982, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2603 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2603 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2603 = Sparse.eval value2603 (momentVector H) := by
  have heq : pivotMatrix2603 = (fun u v => node2603 (pivotPermutation2603 u) v) := by apply Matrix.ext; unfold pivotMatrix2603 node2603 pivotPermutation2603; decide +kernel
  have hmoment : injectiveMoment H node2603 = injectiveMoment H pivotMatrix2603 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2603 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2603 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2603 (0 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2603 (0 : Fin 4) = raw6303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2603 raw6303; decide +kernel
    rw [heq]
    exact (canonical6303 hH).trans (sound985 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2603 (1 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2603 (1 : Fin 4) = raw6524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2603 raw6524; decide +kernel
    rw [heq]
    exact (canonical6524 hH).trans (sound1075 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2603 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2603 (2 : Fin 4) = raw6530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2603 raw6530; decide +kernel
    rw [heq]
    exact (canonical6530 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2603 (3 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2603 (3 : Fin 4) = raw6531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2603 raw6531; decide +kernel
    rw [heq]
    exact (canonical6531 hH).trans (sound1080 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2603 + (injectiveMoment H (mergeFirst pivotMatrix2603 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2603 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2603 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2603 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2603, value1075, value1079, value1080, value985, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2604 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2604 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

theorem sound2604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2604 = Sparse.eval value2604 (momentVector H) := by
  have heq : pivotMatrix2604 = (fun u v => node2604 (pivotPermutation2604 u) v) := by apply Matrix.ext; unfold pivotMatrix2604 node2604 pivotPermutation2604; decide +kernel
  have hmoment : injectiveMoment H node2604 = injectiveMoment H pivotMatrix2604 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2604 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2604 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2604 (0 : Fin 4)) =
      Sparse.eval value960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2604 (0 : Fin 4) = raw6308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2604 raw6308; decide +kernel
    rw [heq]
    exact (canonical6308 hH).trans (sound960 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2604 (1 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2604 (1 : Fin 4) = raw6527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2604 raw6527; decide +kernel
    rw [heq]
    exact (canonical6527 hH).trans (sound797 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2604 (2 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2604 (2 : Fin 4) = raw6534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2604 raw6534; decide +kernel
    rw [heq]
    exact (canonical6534 hH).trans (sound797 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2604 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2604 (3 : Fin 4) = raw6535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2604 raw6535; decide +kernel
    rw [heq]
    exact (canonical6535 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2604 + (injectiveMoment H (mergeFirst pivotMatrix2604 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2604 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2604 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2604 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2604, value1040, value797, value960, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2605 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2605 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem sound2605 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2605 = Sparse.eval value2605 (momentVector H) := by
  have heq : pivotMatrix2605 = (fun u v => node2605 (pivotPermutation2605 u) v) := by apply Matrix.ext; unfold pivotMatrix2605 node2605 pivotPermutation2605; decide +kernel
  have hmoment : injectiveMoment H node2605 = injectiveMoment H pivotMatrix2605 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2605 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2605 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2605 (0 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2605 (0 : Fin 4) = raw6311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2605 raw6311; decide +kernel
    rw [heq]
    exact (canonical6311 hH).trans (sound1268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2605 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2605 (1 : Fin 4) = raw6530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2605 raw6530; decide +kernel
    rw [heq]
    exact (canonical6530 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2605 (2 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2605 (2 : Fin 4) = raw6537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2605 raw6537; decide +kernel
    rw [heq]
    exact (canonical6537 hH).trans (sound1242 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2605 (3 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2605 (3 : Fin 4) = raw6538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2605 raw6538; decide +kernel
    rw [heq]
    exact (canonical6538 hH).trans (sound1081 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2605 + (injectiveMoment H (mergeFirst pivotMatrix2605 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2605 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2605 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2605 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2605, value1079, value1081, value1242, value1268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2606 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2606 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem sound2606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2606 = Sparse.eval value2606 (momentVector H) := by
  have heq : pivotMatrix2606 = (fun u v => node2606 (pivotPermutation2606 u) v) := by apply Matrix.ext; unfold pivotMatrix2606 node2606 pivotPermutation2606; decide +kernel
  have hmoment : injectiveMoment H node2606 = injectiveMoment H pivotMatrix2606 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2606 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2606 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2606 (0 : Fin 4)) =
      Sparse.eval value986 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2606 (0 : Fin 4) = raw6312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2606 raw6312; decide +kernel
    rw [heq]
    exact (canonical6312 hH).trans (sound986 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2606 (1 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2606 (1 : Fin 4) = raw6531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2606 raw6531; decide +kernel
    rw [heq]
    exact (canonical6531 hH).trans (sound1080 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2606 (2 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2606 (2 : Fin 4) = raw6538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2606 raw6538; decide +kernel
    rw [heq]
    exact (canonical6538 hH).trans (sound1081 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2606 (3 : Fin 4)) =
      Sparse.eval value1082 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2606 (3 : Fin 4) = raw6539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2606 raw6539; decide +kernel
    rw [heq]
    exact (canonical6539 hH).trans (sound1082 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2606 + (injectiveMoment H (mergeFirst pivotMatrix2606 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2606 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2606 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2606 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2606, value1080, value1081, value1082, value986, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2607 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2607 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem sound2607 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2607 = Sparse.eval value2607 (momentVector H) := by
  have heq : pivotMatrix2607 = (fun u v => node2607 (pivotPermutation2607 u) v) := by apply Matrix.ext; unfold pivotMatrix2607 node2607 pivotPermutation2607; decide +kernel
  have hmoment : injectiveMoment H node2607 = injectiveMoment H pivotMatrix2607 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2607 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2607 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2607 (0 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2607 (0 : Fin 4) = raw6673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2607 raw6673; decide +kernel
    rw [heq]
    exact (canonical6673 hH).trans (sound1118 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2607 (1 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2607 (1 : Fin 4) = raw6503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2607 raw6503; decide +kernel
    rw [heq]
    exact (canonical6503 hH).trans (sound1054 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2607 (2 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2607 (2 : Fin 4) = raw6488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2607 raw6488; decide +kernel
    rw [heq]
    exact (canonical6488 hH).trans (sound1048 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2607 (3 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2607 (3 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2607 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2607 + (injectiveMoment H (mergeFirst pivotMatrix2607 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2607 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2607 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2607 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2607, value1048, value1054, value1118, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2608 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2608 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem sound2608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2608 = Sparse.eval value2608 (momentVector H) := by
  have heq : pivotMatrix2608 = (fun u v => node2608 (pivotPermutation2608 u) v) := by apply Matrix.ext; unfold pivotMatrix2608 node2608 pivotPermutation2608; decide +kernel
  have hmoment : injectiveMoment H node2608 = injectiveMoment H pivotMatrix2608 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2608 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2608 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2608 (0 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2608 (0 : Fin 4) = raw6675 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2608 raw6675; decide +kernel
    rw [heq]
    exact (canonical6675 hH).trans (sound936 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2608 (1 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2608 (1 : Fin 4) = raw6506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2608 raw6506; decide +kernel
    rw [heq]
    exact (canonical6506 hH).trans (sound1056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2608 (2 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2608 (2 : Fin 4) = raw6490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2608 raw6490; decide +kernel
    rw [heq]
    exact (canonical6490 hH).trans (sound1000 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2608 (3 : Fin 4)) =
      Sparse.eval value1049 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2608 (3 : Fin 4) = raw6489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2608 raw6489; decide +kernel
    rw [heq]
    exact (canonical6489 hH).trans (sound1049 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2608 + (injectiveMoment H (mergeFirst pivotMatrix2608 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2608 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2608 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2608 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2608, value1000, value1049, value1056, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2609 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2609 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem sound2609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2609 = Sparse.eval value2609 (momentVector H) := by
  have heq : pivotMatrix2609 = (fun u v => node2609 (pivotPermutation2609 u) v) := by apply Matrix.ext; unfold pivotMatrix2609 node2609 pivotPermutation2609; decide +kernel
  have hmoment : injectiveMoment H node2609 = injectiveMoment H pivotMatrix2609 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2609 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2609 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2609 (0 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2609 (0 : Fin 4) = raw6676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2609 raw6676; decide +kernel
    rw [heq]
    exact (canonical6676 hH).trans (sound1242 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2609 (1 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2609 (1 : Fin 4) = raw6507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2609 raw6507; decide +kernel
    rw [heq]
    exact (canonical6507 hH).trans (sound1057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2609 (2 : Fin 4)) =
      Sparse.eval value1246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2609 (2 : Fin 4) = raw6491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2609 raw6491; decide +kernel
    rw [heq]
    exact (canonical6491 hH).trans (sound1246 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2609 (3 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2609 (3 : Fin 4) = raw6490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2609 raw6490; decide +kernel
    rw [heq]
    exact (canonical6490 hH).trans (sound1000 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2609 + (injectiveMoment H (mergeFirst pivotMatrix2609 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2609 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2609 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2609 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2609, value1000, value1057, value1242, value1246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2610 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2610 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem sound2610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2610 = Sparse.eval value2610 (momentVector H) := by
  have heq : pivotMatrix2610 = (fun u v => node2610 (pivotPermutation2610 u) v) := by apply Matrix.ext; unfold pivotMatrix2610 node2610 pivotPermutation2610; decide +kernel
  have hmoment : injectiveMoment H node2610 = injectiveMoment H pivotMatrix2610 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2610 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2610 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2610 (0 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2610 (0 : Fin 4) = raw6678 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2610 raw6678; decide +kernel
    rw [heq]
    exact (canonical6678 hH).trans (sound837 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2610 (1 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2610 (1 : Fin 4) = raw6509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2610 raw6509; decide +kernel
    rw [heq]
    exact (canonical6509 hH).trans (sound1059 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2610 (2 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2610 (2 : Fin 4) = raw6493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2610 raw6493; decide +kernel
    rw [heq]
    exact (canonical6493 hH).trans (sound1050 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2610 (3 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2610 (3 : Fin 4) = raw6492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2610 raw6492; decide +kernel
    rw [heq]
    exact (canonical6492 hH).trans (sound1265 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2610 + (injectiveMoment H (mergeFirst pivotMatrix2610 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2610 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2610 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2610 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2610, value1050, value1059, value1265, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2611 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2611 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem sound2611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2611 = Sparse.eval value2611 (momentVector H) := by
  have heq : pivotMatrix2611 = (fun u v => node2611 (pivotPermutation2611 u) v) := by apply Matrix.ext; unfold pivotMatrix2611 node2611 pivotPermutation2611; decide +kernel
  have hmoment : injectiveMoment H node2611 = injectiveMoment H pivotMatrix2611 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2611 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2611 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2611 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2611 (0 : Fin 4) = raw6682 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2611 raw6682; decide +kernel
    rw [heq]
    exact (canonical6682 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2611 (1 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2611 (1 : Fin 4) = raw6517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2611 raw6517; decide +kernel
    rw [heq]
    exact (canonical6517 hH).trans (sound1065 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2611 (2 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2611 (2 : Fin 4) = raw6507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2611 raw6507; decide +kernel
    rw [heq]
    exact (canonical6507 hH).trans (sound1057 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2611 (3 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2611 (3 : Fin 4) = raw6506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2611 raw6506; decide +kernel
    rw [heq]
    exact (canonical6506 hH).trans (sound1056 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2611 + (injectiveMoment H (mergeFirst pivotMatrix2611 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2611 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2611 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2611 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2611, value1056, value1057, value1065, value1079, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2612 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2612 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem sound2612 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2612 = Sparse.eval value2612 (momentVector H) := by
  have heq : pivotMatrix2612 = (fun u v => node2612 (pivotPermutation2612 u) v) := by apply Matrix.ext; unfold pivotMatrix2612 node2612 pivotPermutation2612; decide +kernel
  have hmoment : injectiveMoment H node2612 = injectiveMoment H pivotMatrix2612 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2612 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2612 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2612 (0 : Fin 4)) =
      Sparse.eval value1114 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2612 (0 : Fin 4) = raw6695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2612 raw6695; decide +kernel
    rw [heq]
    exact (canonical6695 hH).trans (sound1114 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2612 (1 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2612 (1 : Fin 4) = raw6541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2612 raw6541; decide +kernel
    rw [heq]
    exact (canonical6541 hH).trans (sound1117 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2612 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2612 (2 : Fin 4) = raw6536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2612 raw6536; decide +kernel
    rw [heq]
    exact (canonical6536 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2612 (3 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2612 (3 : Fin 4) = raw6535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2612 raw6535; decide +kernel
    rw [heq]
    exact (canonical6535 hH).trans (sound1040 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2612 + (injectiveMoment H (mergeFirst pivotMatrix2612 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2612 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2612 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2612 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2612, value1040, value1114, value1117, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2613 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2613 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem sound2613 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2613 = Sparse.eval value2613 (momentVector H) := by
  have heq : pivotMatrix2613 = (fun u v => node2613 (pivotPermutation2613 u) v) := by apply Matrix.ext; unfold pivotMatrix2613 node2613 pivotPermutation2613; decide +kernel
  have hmoment : injectiveMoment H node2613 = injectiveMoment H pivotMatrix2613 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2613 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2613 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2613 (0 : Fin 4)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2613 (0 : Fin 4) = raw7215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2613 raw7215; decide +kernel
    rw [heq]
    exact (canonical7215 hH).trans (sound1264 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2613 (1 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2613 (1 : Fin 4) = raw6544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2613 raw6544; decide +kernel
    rw [heq]
    exact (canonical6544 hH).trans (sound1242 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2613 (2 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2613 (2 : Fin 4) = raw6507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2613 raw6507; decide +kernel
    rw [heq]
    exact (canonical6507 hH).trans (sound1057 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2613 (3 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2613 (3 : Fin 4) = raw6503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2613 raw6503; decide +kernel
    rw [heq]
    exact (canonical6503 hH).trans (sound1054 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2613 + (injectiveMoment H (mergeFirst pivotMatrix2613 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2613 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2613 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2613 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2613, value1054, value1057, value1242, value1264, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2614 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2614 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem sound2614 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2614 = Sparse.eval value2614 (momentVector H) := by
  have heq : pivotMatrix2614 = (fun u v => node2614 (pivotPermutation2614 u) v) := by apply Matrix.ext; unfold pivotMatrix2614 node2614 pivotPermutation2614; decide +kernel
  have hmoment : injectiveMoment H node2614 = injectiveMoment H pivotMatrix2614 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2614 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2614 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2614 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2614 (0 : Fin 4) = raw7216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2614 raw7216; decide +kernel
    rw [heq]
    exact (canonical7216 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2614 (1 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2614 (1 : Fin 4) = raw6545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2614 raw6545; decide +kernel
    rw [heq]
    exact (canonical6545 hH).trans (sound1260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2614 (2 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2614 (2 : Fin 4) = raw6508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2614 raw6508; decide +kernel
    rw [heq]
    exact (canonical6508 hH).trans (sound1058 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2614 (3 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2614 (3 : Fin 4) = raw6505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2614 raw6505; decide +kernel
    rw [heq]
    exact (canonical6505 hH).trans (sound1053 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2614 + (injectiveMoment H (mergeFirst pivotMatrix2614 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2614 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2614 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2614 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2614, value1053, value1058, value1260, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2615 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2615 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem sound2615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2615 = Sparse.eval value2615 (momentVector H) := by
  have heq : pivotMatrix2615 = (fun u v => node2615 (pivotPermutation2615 u) v) := by apply Matrix.ext; unfold pivotMatrix2615 node2615 pivotPermutation2615; decide +kernel
  have hmoment : injectiveMoment H node2615 = injectiveMoment H pivotMatrix2615 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2615 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2615 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2615 (0 : Fin 4)) =
      Sparse.eval value1284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2615 (0 : Fin 4) = raw7351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2615 raw7351; decide +kernel
    rw [heq]
    exact (canonical7351 hH).trans (sound1284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2615 (1 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2615 (1 : Fin 4) = raw6550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2615 raw6550; decide +kernel
    rw [heq]
    exact (canonical6550 hH).trans (sound1083 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2615 (2 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2615 (2 : Fin 4) = raw6509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2615 raw6509; decide +kernel
    rw [heq]
    exact (canonical6509 hH).trans (sound1059 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2615 (3 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2615 (3 : Fin 4) = raw6505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2615 raw6505; decide +kernel
    rw [heq]
    exact (canonical6505 hH).trans (sound1053 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2615 + (injectiveMoment H (mergeFirst pivotMatrix2615 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2615 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2615 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2615 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2615, value1053, value1059, value1083, value1284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2616 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2616 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem sound2616 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2616 = Sparse.eval value2616 (momentVector H) := by
  have heq : pivotMatrix2616 = (fun u v => node2616 (pivotPermutation2616 u) v) := by apply Matrix.ext; unfold pivotMatrix2616 node2616 pivotPermutation2616; decide +kernel
  have hmoment : injectiveMoment H node2616 = injectiveMoment H pivotMatrix2616 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2616 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2616 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2616 (0 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2616 (0 : Fin 4) = raw7219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2616 raw7219; decide +kernel
    rw [heq]
    exact (canonical7219 hH).trans (sound1267 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2616 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2616 (1 : Fin 4) = raw6548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2616 raw6548; decide +kernel
    rw [heq]
    exact (canonical6548 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2616 (2 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2616 (2 : Fin 4) = raw6517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2616 raw6517; decide +kernel
    rw [heq]
    exact (canonical6517 hH).trans (sound1065 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2616 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2616 (3 : Fin 4) = raw6513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2616 raw6513; decide +kernel
    rw [heq]
    exact (canonical6513 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2616 + (injectiveMoment H (mergeFirst pivotMatrix2616 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2616 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2616 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2616 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2616, value1063, value1065, value1079, value1267, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2617 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2617 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem sound2617 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2617 = Sparse.eval value2617 (momentVector H) := by
  have heq : pivotMatrix2617 = (fun u v => node2617 (pivotPermutation2617 u) v) := by apply Matrix.ext; unfold pivotMatrix2617 node2617 pivotPermutation2617; decide +kernel
  have hmoment : injectiveMoment H node2617 = injectiveMoment H pivotMatrix2617 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2617 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2617 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2617 (0 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2617 (0 : Fin 4) = raw7221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2617 raw7221; decide +kernel
    rw [heq]
    exact (canonical7221 hH).trans (sound1268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2617 (1 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2617 (1 : Fin 4) = raw6549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2617 raw6549; decide +kernel
    rw [heq]
    exact (canonical6549 hH).trans (sound1081 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2617 (2 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2617 (2 : Fin 4) = raw6518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2617 raw6518; decide +kernel
    rw [heq]
    exact (canonical6518 hH).trans (sound1066 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2617 (3 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2617 (3 : Fin 4) = raw6516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2617 raw6516; decide +kernel
    rw [heq]
    exact (canonical6516 hH).trans (sound1063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2617 + (injectiveMoment H (mergeFirst pivotMatrix2617 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2617 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2617 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2617 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2617, value1063, value1066, value1081, value1268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2618 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2618 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound2618 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2618 = Sparse.eval value2618 (momentVector H) := by
  have heq : pivotMatrix2618 = (fun u v => node2618 (pivotPermutation2618 u) v) := by apply Matrix.ext; unfold pivotMatrix2618 node2618 pivotPermutation2618; decide +kernel
  have hmoment : injectiveMoment H node2618 = injectiveMoment H pivotMatrix2618 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2618 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2618 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2618 (0 : Fin 4)) =
      Sparse.eval value1349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2618 (0 : Fin 4) = raw7270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2618 raw7270; decide +kernel
    rw [heq]
    exact (canonical7270 hH).trans (sound1349 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2618 (1 : Fin 4)) =
      Sparse.eval value1349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2618 (1 : Fin 4) = raw6590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2618 raw6590; decide +kernel
    rw [heq]
    exact (canonical6590 hH).trans (sound1349 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2618 (2 : Fin 4)) =
      Sparse.eval value1088 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2618 (2 : Fin 4) = raw6585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2618 raw6585; decide +kernel
    rw [heq]
    exact (canonical6585 hH).trans (sound1088 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2618 (3 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2618 (3 : Fin 4) = raw6584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2618 raw6584; decide +kernel
    rw [heq]
    exact (canonical6584 hH).trans (sound1360 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2618 + (injectiveMoment H (mergeFirst pivotMatrix2618 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2618 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2618 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2618 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2618, value1088, value1349, value1360, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2619 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2619 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2619 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2619 = Sparse.eval value2619 (momentVector H) := by
  have heq : pivotMatrix2619 = (fun u v => node2619 (pivotPermutation2619 u) v) := by apply Matrix.ext; unfold pivotMatrix2619 node2619 pivotPermutation2619; decide +kernel
  have hmoment : injectiveMoment H node2619 = injectiveMoment H pivotMatrix2619 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2619 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2619 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2619 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2619 (0 : Fin 4) = raw6919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2619 raw6919; decide +kernel
    rw [heq]
    exact (canonical6919 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2619 (1 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2619 (1 : Fin 4) = raw6612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2619 raw6612; decide +kernel
    rw [heq]
    exact (canonical6612 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2619 (2 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2619 (2 : Fin 4) = raw6600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2619 raw6600; decide +kernel
    rw [heq]
    exact (canonical6600 hH).trans (sound1094 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2619 (3 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2619 (3 : Fin 4) = raw6599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2619 raw6599; decide +kernel
    rw [heq]
    exact (canonical6599 hH).trans (sound1036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2619 + (injectiveMoment H (mergeFirst pivotMatrix2619 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2619 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2619 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2619 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2619, value1036, value1094, value1265, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2620 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2620 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2620 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2620 = Sparse.eval value2620 (momentVector H) := by
  have heq : pivotMatrix2620 = (fun u v => node2620 (pivotPermutation2620 u) v) := by apply Matrix.ext; unfold pivotMatrix2620 node2620 pivotPermutation2620; decide +kernel
  have hmoment : injectiveMoment H node2620 = injectiveMoment H pivotMatrix2620 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2620 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2620 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2620 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2620 (0 : Fin 4) = raw7487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2620 raw7487; decide +kernel
    rw [heq]
    exact (canonical7487 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2620 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2620 (1 : Fin 4) = raw6635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2620 raw6635; decide +kernel
    rw [heq]
    exact (canonical6635 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2620 (2 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2620 (2 : Fin 4) = raw6600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2620 raw6600; decide +kernel
    rw [heq]
    exact (canonical6600 hH).trans (sound1094 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2620 (3 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2620 (3 : Fin 4) = raw6598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2620 raw6598; decide +kernel
    rw [heq]
    exact (canonical6598 hH).trans (sound995 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2620 + (injectiveMoment H (mergeFirst pivotMatrix2620 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2620 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2620 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2620 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2620, value1094, value1110, value1202, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2621 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2621 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem sound2621 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2621 = Sparse.eval value2621 (momentVector H) := by
  have heq : pivotMatrix2621 = (fun u v => node2621 (pivotPermutation2621 u) v) := by apply Matrix.ext; unfold pivotMatrix2621 node2621 pivotPermutation2621; decide +kernel
  have hmoment : injectiveMoment H node2621 = injectiveMoment H pivotMatrix2621 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2621 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2621 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2621 (0 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2621 (0 : Fin 4) = raw6395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2621 raw6395; decide +kernel
    rw [heq]
    exact (canonical6395 hH).trans (sound1198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2621 (1 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2621 (1 : Fin 4) = raw6600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2621 raw6600; decide +kernel
    rw [heq]
    exact (canonical6600 hH).trans (sound1094 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2621 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2621 (2 : Fin 4) = raw6612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2621 raw6612; decide +kernel
    rw [heq]
    exact (canonical6612 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2621 (3 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2621 (3 : Fin 4) = raw6613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2621 raw6613; decide +kernel
    rw [heq]
    exact (canonical6613 hH).trans (sound1099 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2621 + (injectiveMoment H (mergeFirst pivotMatrix2621 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2621 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2621 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2621 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2621, value1094, value1099, value1198, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2622 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2622 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2622 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2622 = Sparse.eval value2622 (momentVector H) := by
  have heq : pivotMatrix2622 = (fun u v => node2622 (pivotPermutation2622 u) v) := by apply Matrix.ext; unfold pivotMatrix2622 node2622 pivotPermutation2622; decide +kernel
  have hmoment : injectiveMoment H node2622 = injectiveMoment H pivotMatrix2622 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2622 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2622 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2622 (0 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2622 (0 : Fin 4) = raw6396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2622 raw6396; decide +kernel
    rw [heq]
    exact (canonical6396 hH).trans (sound998 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2622 (1 : Fin 4)) =
      Sparse.eval value1095 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2622 (1 : Fin 4) = raw6601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2622 raw6601; decide +kernel
    rw [heq]
    exact (canonical6601 hH).trans (sound1095 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2622 (2 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2622 (2 : Fin 4) = raw6613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2622 raw6613; decide +kernel
    rw [heq]
    exact (canonical6613 hH).trans (sound1099 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2622 (3 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2622 (3 : Fin 4) = raw6614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2622 raw6614; decide +kernel
    rw [heq]
    exact (canonical6614 hH).trans (sound1100 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2622 + (injectiveMoment H (mergeFirst pivotMatrix2622 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2622 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2622 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2622 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2622, value1095, value1099, value1100, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2623 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2623 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2623 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2623 = Sparse.eval value2623 (momentVector H) := by
  have heq : pivotMatrix2623 = (fun u v => node2623 (pivotPermutation2623 u) v) := by apply Matrix.ext; unfold pivotMatrix2623 node2623 pivotPermutation2623; decide +kernel
  have hmoment : injectiveMoment H node2623 = injectiveMoment H pivotMatrix2623 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2623 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2623 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2623 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2623 (0 : Fin 4) = raw6921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2623 raw6921; decide +kernel
    rw [heq]
    exact (canonical6921 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2623 (1 : Fin 4)) =
      Sparse.eval value1262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2623 (1 : Fin 4) = raw6617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2623 raw6617; decide +kernel
    rw [heq]
    exact (canonical6617 hH).trans (sound1262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2623 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2623 (2 : Fin 4) = raw6612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2623 raw6612; decide +kernel
    rw [heq]
    exact (canonical6612 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2623 (3 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2623 (3 : Fin 4) = raw6611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2623 raw6611; decide +kernel
    rw [heq]
    exact (canonical6611 hH).trans (sound1078 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2623 + (injectiveMoment H (mergeFirst pivotMatrix2623 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2623 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2623 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2623 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2623, value1009, value1078, value1262, value1265, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
