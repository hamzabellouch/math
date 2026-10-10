import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical262

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2688 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2688 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem sound2688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2688 = Sparse.eval value2688 (momentVector H) := by
  have heq : pivotMatrix2688 = (fun u v => node2688 (pivotPermutation2688 u) v) := by apply Matrix.ext; unfold pivotMatrix2688 node2688 pivotPermutation2688; decide +kernel
  have hmoment : injectiveMoment H node2688 = injectiveMoment H pivotMatrix2688 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2688 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2688 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2688 (0 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2688 (0 : Fin 4) = raw6108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2688 raw6108; decide +kernel
    rw [heq]
    exact (canonical6108 hH).trans (sound787 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2688 (1 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2688 (1 : Fin 4) = raw7019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2688 raw7019; decide +kernel
    rw [heq]
    exact (canonical7019 hH).trans (sound1178 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2688 (2 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2688 (2 : Fin 4) = raw7028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2688 raw7028; decide +kernel
    rw [heq]
    exact (canonical7028 hH).trans (sound1178 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2688 (3 : Fin 4)) =
      Sparse.eval value1186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2688 (3 : Fin 4) = raw7031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2688 raw7031; decide +kernel
    rw [heq]
    exact (canonical7031 hH).trans (sound1186 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2688 + (injectiveMoment H (mergeFirst pivotMatrix2688 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2688 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2688 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2688 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2688, value1178, value1186, value787, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2689 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2689 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem sound2689 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2689 = Sparse.eval value2689 (momentVector H) := by
  have heq : pivotMatrix2689 = (fun u v => node2689 (pivotPermutation2689 u) v) := by apply Matrix.ext; unfold pivotMatrix2689 node2689 pivotPermutation2689; decide +kernel
  have hmoment : injectiveMoment H node2689 = injectiveMoment H pivotMatrix2689 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2689 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2689 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2689 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2689 (0 : Fin 4) = raw7084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2689 raw7084; decide +kernel
    rw [heq]
    exact (canonical7084 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2689 (1 : Fin 4)) =
      Sparse.eval value1175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2689 (1 : Fin 4) = raw7003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2689 raw7003; decide +kernel
    rw [heq]
    exact (canonical7003 hH).trans (sound1175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2689 (2 : Fin 4)) =
      Sparse.eval value1156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2689 (2 : Fin 4) = raw7000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2689 raw7000; decide +kernel
    rw [heq]
    exact (canonical7000 hH).trans (sound1156 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2689 (3 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2689 (3 : Fin 4) = raw6999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2689 raw6999; decide +kernel
    rw [heq]
    exact (canonical6999 hH).trans (sound1173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2689 + (injectiveMoment H (mergeFirst pivotMatrix2689 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2689 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2689 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2689 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2689, value1156, value1173, value1175, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2690 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2690 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem sound2690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2690 = Sparse.eval value2690 (momentVector H) := by
  have heq : pivotMatrix2690 = (fun u v => node2690 (pivotPermutation2690 u) v) := by apply Matrix.ext; unfold pivotMatrix2690 node2690 pivotPermutation2690; decide +kernel
  have hmoment : injectiveMoment H node2690 = injectiveMoment H pivotMatrix2690 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2690 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2690 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2690 (0 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2690 (0 : Fin 4) = raw7098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2690 raw7098; decide +kernel
    rw [heq]
    exact (canonical7098 hH).trans (sound1202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2690 (1 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2690 (1 : Fin 4) = raw7019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2690 raw7019; decide +kernel
    rw [heq]
    exact (canonical7019 hH).trans (sound1178 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2690 (2 : Fin 4)) =
      Sparse.eval value1167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2690 (2 : Fin 4) = raw7013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2690 raw7013; decide +kernel
    rw [heq]
    exact (canonical7013 hH).trans (sound1167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2690 (3 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2690 (3 : Fin 4) = raw7012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2690 raw7012; decide +kernel
    rw [heq]
    exact (canonical7012 hH).trans (sound1176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2690 + (injectiveMoment H (mergeFirst pivotMatrix2690 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2690 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2690 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2690 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2690, value1167, value1176, value1178, value1202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2691 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2691 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem sound2691 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2691 = Sparse.eval value2691 (momentVector H) := by
  have heq : pivotMatrix2691 = (fun u v => node2691 (pivotPermutation2691 u) v) := by apply Matrix.ext; unfold pivotMatrix2691 node2691 pivotPermutation2691; decide +kernel
  have hmoment : injectiveMoment H node2691 = injectiveMoment H pivotMatrix2691 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2691 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2691 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2691 (0 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2691 (0 : Fin 4) = raw7100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2691 raw7100; decide +kernel
    rw [heq]
    exact (canonical7100 hH).trans (sound802 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2691 (1 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2691 (1 : Fin 4) = raw7020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2691 raw7020; decide +kernel
    rw [heq]
    exact (canonical7020 hH).trans (sound1180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2691 (2 : Fin 4)) =
      Sparse.eval value935 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2691 (2 : Fin 4) = raw7015 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2691 raw7015; decide +kernel
    rw [heq]
    exact (canonical7015 hH).trans (sound935 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2691 (3 : Fin 4)) =
      Sparse.eval value768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2691 (3 : Fin 4) = raw7014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2691 raw7014; decide +kernel
    rw [heq]
    exact (canonical7014 hH).trans (sound768 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2691 + (injectiveMoment H (mergeFirst pivotMatrix2691 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2691 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2691 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2691 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2691, value1180, value768, value802, value935, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2692 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2692 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

theorem sound2692 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2692 = Sparse.eval value2692 (momentVector H) := by
  have heq : pivotMatrix2692 = (fun u v => node2692 (pivotPermutation2692 u) v) := by apply Matrix.ext; unfold pivotMatrix2692 node2692 pivotPermutation2692; decide +kernel
  have hmoment : injectiveMoment H node2692 = injectiveMoment H pivotMatrix2692 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2692 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2692 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2692 (0 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2692 (0 : Fin 4) = raw7115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2692 raw7115; decide +kernel
    rw [heq]
    exact (canonical7115 hH).trans (sound967 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2692 (1 : Fin 4)) =
      Sparse.eval value767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2692 (1 : Fin 4) = raw7029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2692 raw7029; decide +kernel
    rw [heq]
    exact (canonical7029 hH).trans (sound767 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2692 (2 : Fin 4)) =
      Sparse.eval value767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2692 (2 : Fin 4) = raw7024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2692 raw7024; decide +kernel
    rw [heq]
    exact (canonical7024 hH).trans (sound767 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2692 (3 : Fin 4)) =
      Sparse.eval value908 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2692 (3 : Fin 4) = raw7023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2692 raw7023; decide +kernel
    rw [heq]
    exact (canonical7023 hH).trans (sound908 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2692 + (injectiveMoment H (mergeFirst pivotMatrix2692 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2692 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2692 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2692 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2692, value767, value908, value967, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2693 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2693 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem sound2693 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2693 = Sparse.eval value2693 (momentVector H) := by
  have heq : pivotMatrix2693 = (fun u v => node2693 (pivotPermutation2693 u) v) := by apply Matrix.ext; unfold pivotMatrix2693 node2693 pivotPermutation2693; decide +kernel
  have hmoment : injectiveMoment H node2693 = injectiveMoment H pivotMatrix2693 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2693 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2693 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2693 (0 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2693 (0 : Fin 4) = raw7116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2693 raw7116; decide +kernel
    rw [heq]
    exact (canonical7116 hH).trans (sound801 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2693 (1 : Fin 4)) =
      Sparse.eval value1186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2693 (1 : Fin 4) = raw7031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2693 raw7031; decide +kernel
    rw [heq]
    exact (canonical7031 hH).trans (sound1186 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2693 (2 : Fin 4)) =
      Sparse.eval value1185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2693 (2 : Fin 4) = raw7025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2693 raw7025; decide +kernel
    rw [heq]
    exact (canonical7025 hH).trans (sound1185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2693 (3 : Fin 4)) =
      Sparse.eval value767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2693 (3 : Fin 4) = raw7024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2693 raw7024; decide +kernel
    rw [heq]
    exact (canonical7024 hH).trans (sound767 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2693 + (injectiveMoment H (mergeFirst pivotMatrix2693 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2693 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2693 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2693 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2693, value1185, value1186, value767, value801, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2694 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2694 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem sound2694 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2694 = Sparse.eval value2694 (momentVector H) := by
  have heq : pivotMatrix2694 = (fun u v => node2694 (pivotPermutation2694 u) v) := by apply Matrix.ext; unfold pivotMatrix2694 node2694 pivotPermutation2694; decide +kernel
  have hmoment : injectiveMoment H node2694 = injectiveMoment H pivotMatrix2694 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2694 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2694 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2694 (0 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2694 (0 : Fin 4) = raw7782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2694 raw7782; decide +kernel
    rw [heq]
    exact (canonical7782 hH).trans (sound803 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2694 (1 : Fin 4)) =
      Sparse.eval value1185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2694 (1 : Fin 4) = raw7034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2694 raw7034; decide +kernel
    rw [heq]
    exact (canonical7034 hH).trans (sound1185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2694 (2 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2694 (2 : Fin 4) = raw7020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2694 raw7020; decide +kernel
    rw [heq]
    exact (canonical7020 hH).trans (sound1180 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2694 (3 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2694 (3 : Fin 4) = raw7018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2694 raw7018; decide +kernel
    rw [heq]
    exact (canonical7018 hH).trans (sound1177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2694 + (injectiveMoment H (mergeFirst pivotMatrix2694 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2694 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2694 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2694 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2694, value1177, value1180, value1185, value803, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2695 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2695 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound2695 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2695 = Sparse.eval value2695 (momentVector H) := by
  have heq : pivotMatrix2695 = (fun u v => node2695 (pivotPermutation2695 u) v) := by apply Matrix.ext; unfold pivotMatrix2695 node2695 pivotPermutation2695; decide +kernel
  have hmoment : injectiveMoment H node2695 = injectiveMoment H pivotMatrix2695 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2695 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2695 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2695 (0 : Fin 4)) =
      Sparse.eval value1101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2695 (0 : Fin 4) = raw7773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2695 raw7773; decide +kernel
    rw [heq]
    exact (canonical7773 hH).trans (sound1101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2695 (1 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2695 (1 : Fin 4) = raw7059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2695 raw7059; decide +kernel
    rw [heq]
    exact (canonical7059 hH).trans (sound1028 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2695 (2 : Fin 4)) =
      Sparse.eval value1103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2695 (2 : Fin 4) = raw7058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2695 raw7058; decide +kernel
    rw [heq]
    exact (canonical7058 hH).trans (sound1103 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2695 (3 : Fin 4)) =
      Sparse.eval value1103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2695 (3 : Fin 4) = raw7057 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2695 raw7057; decide +kernel
    rw [heq]
    exact (canonical7057 hH).trans (sound1103 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2695 + (injectiveMoment H (mergeFirst pivotMatrix2695 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2695 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2695 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2695 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2695, value1028, value1101, value1103, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2696 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2696 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2696 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2696 = Sparse.eval value2696 (momentVector H) := by
  have heq : pivotMatrix2696 = (fun u v => node2696 (pivotPermutation2696 u) v) := by apply Matrix.ext; unfold pivotMatrix2696 node2696 pivotPermutation2696; decide +kernel
  have hmoment : injectiveMoment H node2696 = injectiveMoment H pivotMatrix2696 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2696 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2696 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2696 (0 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2696 (0 : Fin 4) = raw7161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2696 raw7161; decide +kernel
    rw [heq]
    exact (canonical7161 hH).trans (sound1008 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2696 (1 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2696 (1 : Fin 4) = raw7069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2696 raw7069; decide +kernel
    rw [heq]
    exact (canonical7069 hH).trans (sound951 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2696 (2 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2696 (2 : Fin 4) = raw7065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2696 raw7065; decide +kernel
    rw [heq]
    exact (canonical7065 hH).trans (sound806 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2696 (3 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2696 (3 : Fin 4) = raw7064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2696 raw7064; decide +kernel
    rw [heq]
    exact (canonical7064 hH).trans (sound1190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2696 + (injectiveMoment H (mergeFirst pivotMatrix2696 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2696 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2696 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2696 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2696, value1008, value1190, value806, value951, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2697 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2697 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2697 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2697 = Sparse.eval value2697 (momentVector H) := by
  have heq : pivotMatrix2697 = (fun u v => node2697 (pivotPermutation2697 u) v) := by apply Matrix.ext; unfold pivotMatrix2697 node2697 pivotPermutation2697; decide +kernel
  have hmoment : injectiveMoment H node2697 = injectiveMoment H pivotMatrix2697 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2697 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2697 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2697 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2697 (0 : Fin 4) = raw7162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2697 raw7162; decide +kernel
    rw [heq]
    exact (canonical7162 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2697 (1 : Fin 4)) =
      Sparse.eval value1193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2697 (1 : Fin 4) = raw7070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2697 raw7070; decide +kernel
    rw [heq]
    exact (canonical7070 hH).trans (sound1193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2697 (2 : Fin 4)) =
      Sparse.eval value1191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2697 (2 : Fin 4) = raw7066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2697 raw7066; decide +kernel
    rw [heq]
    exact (canonical7066 hH).trans (sound1191 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2697 (3 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2697 (3 : Fin 4) = raw7065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2697 raw7065; decide +kernel
    rw [heq]
    exact (canonical7065 hH).trans (sound806 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2697 + (injectiveMoment H (mergeFirst pivotMatrix2697 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2697 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2697 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2697 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2697, value1057, value1191, value1193, value806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2698 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2698 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2698 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2698 = Sparse.eval value2698 (momentVector H) := by
  have heq : pivotMatrix2698 = (fun u v => node2698 (pivotPermutation2698 u) v) := by apply Matrix.ext; unfold pivotMatrix2698 node2698 pivotPermutation2698; decide +kernel
  have hmoment : injectiveMoment H node2698 = injectiveMoment H pivotMatrix2698 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2698 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2698 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2698 (0 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2698 (0 : Fin 4) = raw7774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2698 raw7774; decide +kernel
    rw [heq]
    exact (canonical7774 hH).trans (sound977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2698 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2698 (1 : Fin 4) = raw7081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2698 raw7081; decide +kernel
    rw [heq]
    exact (canonical7081 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2698 (2 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2698 (2 : Fin 4) = raw7069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2698 raw7069; decide +kernel
    rw [heq]
    exact (canonical7069 hH).trans (sound951 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2698 (3 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2698 (3 : Fin 4) = raw7068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2698 raw7068; decide +kernel
    rw [heq]
    exact (canonical7068 hH).trans (sound950 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2698 + (injectiveMoment H (mergeFirst pivotMatrix2698 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2698 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2698 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2698 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2698, value950, value951, value974, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2699 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2699 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2699 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2699 = Sparse.eval value2699 (momentVector H) := by
  have heq : pivotMatrix2699 = (fun u v => node2699 (pivotPermutation2699 u) v) := by apply Matrix.ext; unfold pivotMatrix2699 node2699 pivotPermutation2699; decide +kernel
  have hmoment : injectiveMoment H node2699 = injectiveMoment H pivotMatrix2699 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2699 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2699 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2699 (0 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2699 (0 : Fin 4) = raw7810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2699 raw7810; decide +kernel
    rw [heq]
    exact (canonical7810 hH).trans (sound1207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2699 (1 : Fin 4)) =
      Sparse.eval value1212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2699 (1 : Fin 4) = raw7087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2699 raw7087; decide +kernel
    rw [heq]
    exact (canonical7087 hH).trans (sound1212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2699 (2 : Fin 4)) =
      Sparse.eval value1193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2699 (2 : Fin 4) = raw7070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2699 raw7070; decide +kernel
    rw [heq]
    exact (canonical7070 hH).trans (sound1193 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2699 (3 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2699 (3 : Fin 4) = raw7068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2699 raw7068; decide +kernel
    rw [heq]
    exact (canonical7068 hH).trans (sound950 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2699 + (injectiveMoment H (mergeFirst pivotMatrix2699 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2699 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2699 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2699 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2699, value1193, value1207, value1212, value950, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2700 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2700 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2700 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2700 = Sparse.eval value2700 (momentVector H) := by
  have heq : pivotMatrix2700 = (fun u v => node2700 (pivotPermutation2700 u) v) := by apply Matrix.ext; unfold pivotMatrix2700 node2700 pivotPermutation2700; decide +kernel
  have hmoment : injectiveMoment H node2700 = injectiveMoment H pivotMatrix2700 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2700 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2700 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2700 (0 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2700 (0 : Fin 4) = raw6077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2700 raw6077; decide +kernel
    rw [heq]
    exact (canonical6077 hH).trans (sound910 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2700 (1 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2700 (1 : Fin 4) = raw7078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2700 raw7078; decide +kernel
    rw [heq]
    exact (canonical7078 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2700 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2700 (2 : Fin 4) = raw7094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2700 raw7094; decide +kernel
    rw [heq]
    exact (canonical7094 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2700 (3 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2700 (3 : Fin 4) = raw7098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2700 raw7098; decide +kernel
    rw [heq]
    exact (canonical7098 hH).trans (sound1202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2700 + (injectiveMoment H (mergeFirst pivotMatrix2700 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2700 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2700 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2700 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2700, value1202, value1203, value271, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2701 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2701 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2701 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2701 = Sparse.eval value2701 (momentVector H) := by
  have heq : pivotMatrix2701 = (fun u v => node2701 (pivotPermutation2701 u) v) := by apply Matrix.ext; unfold pivotMatrix2701 node2701 pivotPermutation2701; decide +kernel
  have hmoment : injectiveMoment H node2701 = injectiveMoment H pivotMatrix2701 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2701 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2701 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2701 (0 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2701 (0 : Fin 4) = raw6088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2701 raw6088; decide +kernel
    rw [heq]
    exact (canonical6088 hH).trans (sound915 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2701 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2701 (1 : Fin 4) = raw7081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2701 raw7081; decide +kernel
    rw [heq]
    exact (canonical7081 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2701 (2 : Fin 4)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2701 (2 : Fin 4) = raw7102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2701 raw7102; decide +kernel
    rw [heq]
    exact (canonical7102 hH).trans (sound57 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2701 (3 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2701 (3 : Fin 4) = raw7103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2701 raw7103; decide +kernel
    rw [heq]
    exact (canonical7103 hH).trans (sound1221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2701 + (injectiveMoment H (mergeFirst pivotMatrix2701 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2701 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2701 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2701 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2701, value1221, value57, value915, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2702 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2702 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound2702 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2702 = Sparse.eval value2702 (momentVector H) := by
  have heq : pivotMatrix2702 = (fun u v => node2702 (pivotPermutation2702 u) v) := by apply Matrix.ext; unfold pivotMatrix2702 node2702 pivotPermutation2702; decide +kernel
  have hmoment : injectiveMoment H node2702 = injectiveMoment H pivotMatrix2702 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2702 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2702 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2702 (0 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2702 (0 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2702 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2702 (1 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2702 (1 : Fin 4) = raw7069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2702 raw7069; decide +kernel
    rw [heq]
    exact (canonical7069 hH).trans (sound951 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2702 (2 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2702 (2 : Fin 4) = raw7081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2702 raw7081; decide +kernel
    rw [heq]
    exact (canonical7081 hH).trans (sound974 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2702 (3 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2702 (3 : Fin 4) = raw7083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2702 raw7083; decide +kernel
    rw [heq]
    exact (canonical7083 hH).trans (sound1208 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2702 + (injectiveMoment H (mergeFirst pivotMatrix2702 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2702 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2702 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2702 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2702, value1208, value945, value951, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2703 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2703 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2703 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2703 = Sparse.eval value2703 (momentVector H) := by
  have heq : pivotMatrix2703 = (fun u v => node2703 (pivotPermutation2703 u) v) := by apply Matrix.ext; unfold pivotMatrix2703 node2703 pivotPermutation2703; decide +kernel
  have hmoment : injectiveMoment H node2703 = injectiveMoment H pivotMatrix2703 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2703 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2703 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2703 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2703 (0 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2703 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2703 (1 : Fin 4)) =
      Sparse.eval value1193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2703 (1 : Fin 4) = raw7070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2703 raw7070; decide +kernel
    rw [heq]
    exact (canonical7070 hH).trans (sound1193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2703 (2 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2703 (2 : Fin 4) = raw7082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2703 raw7082; decide +kernel
    rw [heq]
    exact (canonical7082 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2703 (3 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2703 (3 : Fin 4) = raw7084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2703 raw7084; decide +kernel
    rw [heq]
    exact (canonical7084 hH).trans (sound807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2703 + (injectiveMoment H (mergeFirst pivotMatrix2703 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2703 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2703 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2703 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2703, value1193, value1207, value807, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2704 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2704 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2704 = Sparse.eval value2704 (momentVector H) := by
  have heq : pivotMatrix2704 = (fun u v => node2704 (pivotPermutation2704 u) v) := by apply Matrix.ext; unfold pivotMatrix2704 node2704 pivotPermutation2704; decide +kernel
  have hmoment : injectiveMoment H node2704 = injectiveMoment H pivotMatrix2704 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2704 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2704 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2704 (0 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (0 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2704 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (1 : Fin 4) = raw7081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw7081; decide +kernel
    rw [heq]
    exact (canonical7081 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2704 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (2 : Fin 4) = raw7094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw7094; decide +kernel
    rw [heq]
    exact (canonical7094 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2704 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (3 : Fin 4) = raw7097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw7097; decide +kernel
    rw [heq]
    exact (canonical7097 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2704 + (injectiveMoment H (mergeFirst pivotMatrix2704 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2704 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2704 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2704 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2704, value271, value969, value970, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2705 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2705 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2705 = Sparse.eval value2705 (momentVector H) := by
  have heq : pivotMatrix2705 = (fun u v => node2705 (pivotPermutation2705 u) v) := by apply Matrix.ext; unfold pivotMatrix2705 node2705 pivotPermutation2705; decide +kernel
  have hmoment : injectiveMoment H node2705 = injectiveMoment H pivotMatrix2705 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2705 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2705 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2705 (0 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2705 (0 : Fin 4) = raw6278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2705 raw6278; decide +kernel
    rw [heq]
    exact (canonical6278 hH).trans (sound969 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2705 (1 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2705 (1 : Fin 4) = raw7082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2705 raw7082; decide +kernel
    rw [heq]
    exact (canonical7082 hH).trans (sound1207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2705 (2 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2705 (2 : Fin 4) = raw7095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2705 raw7095; decide +kernel
    rw [heq]
    exact (canonical7095 hH).trans (sound272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2705 (3 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2705 (3 : Fin 4) = raw7098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2705 raw7098; decide +kernel
    rw [heq]
    exact (canonical7098 hH).trans (sound1202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2705 + (injectiveMoment H (mergeFirst pivotMatrix2705 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2705 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2705 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2705 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2705, value1202, value1207, value272, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2706 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2706 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem sound2706 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2706 = Sparse.eval value2706 (momentVector H) := by
  have heq : pivotMatrix2706 = (fun u v => node2706 (pivotPermutation2706 u) v) := by apply Matrix.ext; unfold pivotMatrix2706 node2706 pivotPermutation2706; decide +kernel
  have hmoment : injectiveMoment H node2706 = injectiveMoment H pivotMatrix2706 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2706 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2706 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2706 (0 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2706 (0 : Fin 4) = raw6280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2706 raw6280; decide +kernel
    rw [heq]
    exact (canonical6280 hH).trans (sound942 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2706 (1 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2706 (1 : Fin 4) = raw7083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2706 raw7083; decide +kernel
    rw [heq]
    exact (canonical7083 hH).trans (sound1208 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2706 (2 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2706 (2 : Fin 4) = raw7097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2706 raw7097; decide +kernel
    rw [heq]
    exact (canonical7097 hH).trans (sound969 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2706 (3 : Fin 4)) =
      Sparse.eval value971 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2706 (3 : Fin 4) = raw7099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2706 raw7099; decide +kernel
    rw [heq]
    exact (canonical7099 hH).trans (sound971 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2706 + (injectiveMoment H (mergeFirst pivotMatrix2706 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2706 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2706 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2706 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2706, value1208, value942, value969, value971, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2707 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2707 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem sound2707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2707 = Sparse.eval value2707 (momentVector H) := by
  have heq : pivotMatrix2707 = (fun u v => node2707 (pivotPermutation2707 u) v) := by apply Matrix.ext; unfold pivotMatrix2707 node2707 pivotPermutation2707; decide +kernel
  have hmoment : injectiveMoment H node2707 = injectiveMoment H pivotMatrix2707 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2707 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2707 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2707 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2707 (0 : Fin 4) = raw7180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2707 raw7180; decide +kernel
    rw [heq]
    exact (canonical7180 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2707 (1 : Fin 4)) =
      Sparse.eval value1214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2707 (1 : Fin 4) = raw7088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2707 raw7088; decide +kernel
    rw [heq]
    exact (canonical7088 hH).trans (sound1214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2707 (2 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2707 (2 : Fin 4) = raw7084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2707 raw7084; decide +kernel
    rw [heq]
    exact (canonical7084 hH).trans (sound807 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2707 (3 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2707 (3 : Fin 4) = raw7083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2707 raw7083; decide +kernel
    rw [heq]
    exact (canonical7083 hH).trans (sound1208 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2707 + (injectiveMoment H (mergeFirst pivotMatrix2707 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2707 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2707 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2707 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2707, value1009, value1208, value1214, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2708 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2708 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem sound2708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2708 = Sparse.eval value2708 (momentVector H) := by
  have heq : pivotMatrix2708 = (fun u v => node2708 (pivotPermutation2708 u) v) := by apply Matrix.ext; unfold pivotMatrix2708 node2708 pivotPermutation2708; decide +kernel
  have hmoment : injectiveMoment H node2708 = injectiveMoment H pivotMatrix2708 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2708 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2708 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2708 (0 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2708 (0 : Fin 4) = raw7211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2708 raw7211; decide +kernel
    rw [heq]
    exact (canonical7211 hH).trans (sound1048 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2708 (1 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2708 (1 : Fin 4) = raw7103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2708 raw7103; decide +kernel
    rw [heq]
    exact (canonical7103 hH).trans (sound1221 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2708 (2 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2708 (2 : Fin 4) = raw7098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2708 raw7098; decide +kernel
    rw [heq]
    exact (canonical7098 hH).trans (sound1202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2708 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2708 (3 : Fin 4) = raw7097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2708 raw7097; decide +kernel
    rw [heq]
    exact (canonical7097 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2708 + (injectiveMoment H (mergeFirst pivotMatrix2708 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2708 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2708 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2708 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2708, value1048, value1202, value1221, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2709 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2709 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem sound2709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2709 = Sparse.eval value2709 (momentVector H) := by
  have heq : pivotMatrix2709 = (fun u v => node2709 (pivotPermutation2709 u) v) := by apply Matrix.ext; unfold pivotMatrix2709 node2709 pivotPermutation2709; decide +kernel
  have hmoment : injectiveMoment H node2709 = injectiveMoment H pivotMatrix2709 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2709 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2709 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2709 (0 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2709 (0 : Fin 4) = raw7212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2709 raw7212; decide +kernel
    rw [heq]
    exact (canonical7212 hH).trans (sound1000 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2709 (1 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2709 (1 : Fin 4) = raw7105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2709 raw7105; decide +kernel
    rw [heq]
    exact (canonical7105 hH).trans (sound1223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2709 (2 : Fin 4)) =
      Sparse.eval value802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2709 (2 : Fin 4) = raw7100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2709 raw7100; decide +kernel
    rw [heq]
    exact (canonical7100 hH).trans (sound802 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2709 (3 : Fin 4)) =
      Sparse.eval value971 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2709 (3 : Fin 4) = raw7099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2709 raw7099; decide +kernel
    rw [heq]
    exact (canonical7099 hH).trans (sound971 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2709 + (injectiveMoment H (mergeFirst pivotMatrix2709 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2709 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2709 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2709 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2709, value1000, value1223, value802, value971, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2710 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2710 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem sound2710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2710 = Sparse.eval value2710 (momentVector H) := by
  have heq : pivotMatrix2710 = (fun u v => node2710 (pivotPermutation2710 u) v) := by apply Matrix.ext; unfold pivotMatrix2710 node2710 pivotPermutation2710; decide +kernel
  have hmoment : injectiveMoment H node2710 = injectiveMoment H pivotMatrix2710 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2710 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2710 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2710 (0 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2710 (0 : Fin 4) = raw7782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2710 raw7782; decide +kernel
    rw [heq]
    exact (canonical7782 hH).trans (sound803 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2710 (1 : Fin 4)) =
      Sparse.eval value801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2710 (1 : Fin 4) = raw7118 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2710 raw7118; decide +kernel
    rw [heq]
    exact (canonical7118 hH).trans (sound801 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2710 (2 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2710 (2 : Fin 4) = raw7105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2710 raw7105; decide +kernel
    rw [heq]
    exact (canonical7105 hH).trans (sound1223 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2710 (3 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2710 (3 : Fin 4) = raw7103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2710 raw7103; decide +kernel
    rw [heq]
    exact (canonical7103 hH).trans (sound1221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2710 + (injectiveMoment H (mergeFirst pivotMatrix2710 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2710 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2710 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2710 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2710, value1221, value1223, value801, value803, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2711 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2711 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem sound2711 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2711 = Sparse.eval value2711 (momentVector H) := by
  have heq : pivotMatrix2711 = (fun u v => node2711 (pivotPermutation2711 u) v) := by apply Matrix.ext; unfold pivotMatrix2711 node2711 pivotPermutation2711; decide +kernel
  have hmoment : injectiveMoment H node2711 = injectiveMoment H pivotMatrix2711 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2711 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2711 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2711 (0 : Fin 4)) =
      Sparse.eval value1330 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2711 (0 : Fin 4) = raw7797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2711 raw7797; decide +kernel
    rw [heq]
    exact (canonical7797 hH).trans (sound1330 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2711 (1 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2711 (1 : Fin 4) = raw7152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2711 raw7152; decide +kernel
    rw [heq]
    exact (canonical7152 hH).trans (sound685 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2711 (2 : Fin 4)) =
      Sparse.eval value1362 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2711 (2 : Fin 4) = raw7143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2711 raw7143; decide +kernel
    rw [heq]
    exact (canonical7143 hH).trans (sound1362 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2711 (3 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2711 (3 : Fin 4) = raw7141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2711 raw7141; decide +kernel
    rw [heq]
    exact (canonical7141 hH).trans (sound1360 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2711 + (injectiveMoment H (mergeFirst pivotMatrix2711 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2711 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2711 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2711 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2711, value1330, value1360, value1362, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2712 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem sound2712 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2712 = Sparse.eval value2712 (momentVector H) := by
  have heq : pivotMatrix2712 = (fun u v => node2712 (pivotPermutation2712 u) v) := by apply Matrix.ext; unfold pivotMatrix2712 node2712 pivotPermutation2712; decide +kernel
  have hmoment : injectiveMoment H node2712 = injectiveMoment H pivotMatrix2712 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2712 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2712 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2712 (0 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2712 (0 : Fin 4) = raw4611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2712 raw4611; decide +kernel
    rw [heq]
    exact (canonical4611 hH).trans (sound685 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2712 (1 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2712 (1 : Fin 4) = raw7152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2712 raw7152; decide +kernel
    rw [heq]
    exact (canonical7152 hH).trans (sound685 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2712 (2 : Fin 4)) =
      Sparse.eval value1261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2712 (2 : Fin 4) = raw7224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2712 raw7224; decide +kernel
    rw [heq]
    exact (canonical7224 hH).trans (sound1261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2712 (3 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2712 (3 : Fin 4) = raw7230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2712 raw7230; decide +kernel
    rw [heq]
    exact (canonical7230 hH).trans (sound1263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2712 + (injectiveMoment H (mergeFirst pivotMatrix2712 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2712 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2712 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2712 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2712, value1261, value1263, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2713 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2713 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem sound2713 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2713 = Sparse.eval value2713 (momentVector H) := by
  have heq : pivotMatrix2713 = (fun u v => node2713 (pivotPermutation2713 u) v) := by apply Matrix.ext; unfold pivotMatrix2713 node2713 pivotPermutation2713; decide +kernel
  have hmoment : injectiveMoment H node2713 = injectiveMoment H pivotMatrix2713 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2713 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2713 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2713 (0 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2713 (0 : Fin 4) = raw8309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2713 raw8309; decide +kernel
    rw [heq]
    exact (canonical8309 hH).trans (sound1094 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2713 (1 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2713 (1 : Fin 4) = raw7219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2713 raw7219; decide +kernel
    rw [heq]
    exact (canonical7219 hH).trans (sound1267 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2713 (2 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2713 (2 : Fin 4) = raw7151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2713 raw7151; decide +kernel
    rw [heq]
    exact (canonical7151 hH).trans (sound1094 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2713 (3 : Fin 4)) =
      Sparse.eval value475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2713 (3 : Fin 4) = raw7147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2713 raw7147; decide +kernel
    rw [heq]
    exact (canonical7147 hH).trans (sound475 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2713 + (injectiveMoment H (mergeFirst pivotMatrix2713 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2713 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2713 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2713 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2713, value1094, value1267, value475, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2714 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2714 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound2714 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2714 = Sparse.eval value2714 (momentVector H) := by
  have heq : pivotMatrix2714 = (fun u v => node2714 (pivotPermutation2714 u) v) := by apply Matrix.ext; unfold pivotMatrix2714 node2714 pivotPermutation2714; decide +kernel
  have hmoment : injectiveMoment H node2714 = injectiveMoment H pivotMatrix2714 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2714 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2714 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2714 (0 : Fin 4)) =
      Sparse.eval value1092 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2714 (0 : Fin 4) = raw7807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2714 raw7807; decide +kernel
    rw [heq]
    exact (canonical7807 hH).trans (sound1092 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2714 (1 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2714 (1 : Fin 4) = raw7153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2714 raw7153; decide +kernel
    rw [heq]
    exact (canonical7153 hH).trans (sound995 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2714 (2 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2714 (2 : Fin 4) = raw7151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2714 raw7151; decide +kernel
    rw [heq]
    exact (canonical7151 hH).trans (sound1094 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2714 (3 : Fin 4)) =
      Sparse.eval value933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2714 (3 : Fin 4) = raw7150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2714 raw7150; decide +kernel
    rw [heq]
    exact (canonical7150 hH).trans (sound933 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2714 + (injectiveMoment H (mergeFirst pivotMatrix2714 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2714 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2714 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2714 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2714, value1092, value1094, value933, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2715 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2715 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2715 = Sparse.eval value2715 (momentVector H) := by
  have heq : pivotMatrix2715 = (fun u v => node2715 (pivotPermutation2715 u) v) := by apply Matrix.ext; unfold pivotMatrix2715 node2715 pivotPermutation2715; decide +kernel
  have hmoment : injectiveMoment H node2715 = injectiveMoment H pivotMatrix2715 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2715 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2715 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2715 (0 : Fin 4)) =
      Sparse.eval value1189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2715 (0 : Fin 4) = raw7808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2715 raw7808; decide +kernel
    rw [heq]
    exact (canonical7808 hH).trans (sound1189 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2715 (1 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2715 (1 : Fin 4) = raw7169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2715 raw7169; decide +kernel
    rw [heq]
    exact (canonical7169 hH).trans (sound1168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2715 (2 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2715 (2 : Fin 4) = raw7155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2715 raw7155; decide +kernel
    rw [heq]
    exact (canonical7155 hH).trans (sound1037 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2715 (3 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2715 (3 : Fin 4) = raw7154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2715 raw7154; decide +kernel
    rw [heq]
    exact (canonical7154 hH).trans (sound1155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2715 + (injectiveMoment H (mergeFirst pivotMatrix2715 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2715 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2715 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2715 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2715, value1037, value1155, value1168, value1189, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2716 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2716 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2716 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2716 = Sparse.eval value2716 (momentVector H) := by
  have heq : pivotMatrix2716 = (fun u v => node2716 (pivotPermutation2716 u) v) := by apply Matrix.ext; unfold pivotMatrix2716 node2716 pivotPermutation2716; decide +kernel
  have hmoment : injectiveMoment H node2716 = injectiveMoment H pivotMatrix2716 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2716 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2716 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2716 (0 : Fin 4)) =
      Sparse.eval value1189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2716 (0 : Fin 4) = raw7060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2716 raw7060; decide +kernel
    rw [heq]
    exact (canonical7060 hH).trans (sound1189 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2716 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2716 (1 : Fin 4) = raw7155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2716 raw7155; decide +kernel
    rw [heq]
    exact (canonical7155 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2716 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2716 (2 : Fin 4) = raw7159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2716 raw7159; decide +kernel
    rw [heq]
    exact (canonical7159 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2716 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2716 (3 : Fin 4) = raw7160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2716 raw7160; decide +kernel
    rw [heq]
    exact (canonical7160 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2716 + (injectiveMoment H (mergeFirst pivotMatrix2716 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2716 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2716 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2716 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2716, value1037, value1079, value1189, value1234, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2717 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2717 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2717 = Sparse.eval value2717 (momentVector H) := by
  have heq : pivotMatrix2717 = (fun u v => node2717 (pivotPermutation2717 u) v) := by apply Matrix.ext; unfold pivotMatrix2717 node2717 pivotPermutation2717; decide +kernel
  have hmoment : injectiveMoment H node2717 = injectiveMoment H pivotMatrix2717 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2717 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2717 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2717 (0 : Fin 4)) =
      Sparse.eval value1283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (0 : Fin 4) = raw7809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7809; decide +kernel
    rw [heq]
    exact (canonical7809 hH).trans (sound1283 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2717 (1 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (1 : Fin 4) = raw7171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7171; decide +kernel
    rw [heq]
    exact (canonical7171 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2717 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (2 : Fin 4) = raw7159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7159; decide +kernel
    rw [heq]
    exact (canonical7159 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2717 (3 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2717 (3 : Fin 4) = raw7158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2717 raw7158; decide +kernel
    rw [heq]
    exact (canonical7158 hH).trans (sound1016 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2717 + (injectiveMoment H (mergeFirst pivotMatrix2717 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2717 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2717 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2717 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2717, value1016, value1079, value1203, value1283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2718 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2718 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2718 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2718 = Sparse.eval value2718 (momentVector H) := by
  have heq : pivotMatrix2718 = (fun u v => node2718 (pivotPermutation2718 u) v) := by apply Matrix.ext; unfold pivotMatrix2718 node2718 pivotPermutation2718; decide +kernel
  have hmoment : injectiveMoment H node2718 = injectiveMoment H pivotMatrix2718 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2718 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2718 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2718 (0 : Fin 4)) =
      Sparse.eval value1191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2718 (0 : Fin 4) = raw7066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2718 raw7066; decide +kernel
    rw [heq]
    exact (canonical7066 hH).trans (sound1191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2718 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2718 (1 : Fin 4) = raw7159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2718 raw7159; decide +kernel
    rw [heq]
    exact (canonical7159 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2718 (2 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2718 (2 : Fin 4) = raw7162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2718 raw7162; decide +kernel
    rw [heq]
    exact (canonical7162 hH).trans (sound1057 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2718 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2718 (3 : Fin 4) = raw7163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2718 raw7163; decide +kernel
    rw [heq]
    exact (canonical7163 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2718 + (injectiveMoment H (mergeFirst pivotMatrix2718 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2718 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2718 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2718 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2718, value1057, value1079, value1191, value1235, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2719 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2719 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2719 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2719 = Sparse.eval value2719 (momentVector H) := by
  have heq : pivotMatrix2719 = (fun u v => node2719 (pivotPermutation2719 u) v) := by apply Matrix.ext; unfold pivotMatrix2719 node2719 pivotPermutation2719; decide +kernel
  have hmoment : injectiveMoment H node2719 = injectiveMoment H pivotMatrix2719 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2719 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2719 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2719 (0 : Fin 4)) =
      Sparse.eval value1299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2719 (0 : Fin 4) = raw7835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2719 raw7835; decide +kernel
    rw [heq]
    exact (canonical7835 hH).trans (sound1299 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2719 (1 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2719 (1 : Fin 4) = raw7182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2719 raw7182; decide +kernel
    rw [heq]
    exact (canonical7182 hH).trans (sound1206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2719 (2 : Fin 4)) =
      Sparse.eval value1296 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2719 (2 : Fin 4) = raw7165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2719 raw7165; decide +kernel
    rw [heq]
    exact (canonical7165 hH).trans (sound1296 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2719 (3 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2719 (3 : Fin 4) = raw7164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2719 raw7164; decide +kernel
    rw [heq]
    exact (canonical7164 hH).trans (sound1007 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2719 + (injectiveMoment H (mergeFirst pivotMatrix2719 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2719 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2719 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2719 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2719, value1007, value1206, value1296, value1299, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2720 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2720 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2720 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2720 = Sparse.eval value2720 (momentVector H) := by
  have heq : pivotMatrix2720 = (fun u v => node2720 (pivotPermutation2720 u) v) := by apply Matrix.ext; unfold pivotMatrix2720 node2720 pivotPermutation2720; decide +kernel
  have hmoment : injectiveMoment H node2720 = injectiveMoment H pivotMatrix2720 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2720 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2720 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2720 (0 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2720 (0 : Fin 4) = raw6396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2720 raw6396; decide +kernel
    rw [heq]
    exact (canonical6396 hH).trans (sound998 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2720 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2720 (1 : Fin 4) = raw7155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2720 raw7155; decide +kernel
    rw [heq]
    exact (canonical7155 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2720 (2 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2720 (2 : Fin 4) = raw7169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2720 raw7169; decide +kernel
    rw [heq]
    exact (canonical7169 hH).trans (sound1168 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2720 (3 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2720 (3 : Fin 4) = raw7170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2720 raw7170; decide +kernel
    rw [heq]
    exact (canonical7170 hH).trans (sound998 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2720 + (injectiveMoment H (mergeFirst pivotMatrix2720 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2720 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2720 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2720 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2720, value1037, value1168, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2721 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2721 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2721 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2721 = Sparse.eval value2721 (momentVector H) := by
  have heq : pivotMatrix2721 = (fun u v => node2721 (pivotPermutation2721 u) v) := by apply Matrix.ext; unfold pivotMatrix2721 node2721 pivotPermutation2721; decide +kernel
  have hmoment : injectiveMoment H node2721 = injectiveMoment H pivotMatrix2721 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2721 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2721 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2721 (0 : Fin 4)) =
      Sparse.eval value1095 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2721 (0 : Fin 4) = raw7812 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2721 raw7812; decide +kernel
    rw [heq]
    exact (canonical7812 hH).trans (sound1095 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2721 (1 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2721 (1 : Fin 4) = raw7189 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2721 raw7189; decide +kernel
    rw [heq]
    exact (canonical7189 hH).trans (sound1178 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2721 (2 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2721 (2 : Fin 4) = raw7170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2721 raw7170; decide +kernel
    rw [heq]
    exact (canonical7170 hH).trans (sound998 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2721 (3 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2721 (3 : Fin 4) = raw7169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2721 raw7169; decide +kernel
    rw [heq]
    exact (canonical7169 hH).trans (sound1168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2721 + (injectiveMoment H (mergeFirst pivotMatrix2721 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2721 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2721 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2721 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2721, value1095, value1168, value1178, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2722 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2722 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem sound2722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2722 = Sparse.eval value2722 (momentVector H) := by
  have heq : pivotMatrix2722 = (fun u v => node2722 (pivotPermutation2722 u) v) := by apply Matrix.ext; unfold pivotMatrix2722 node2722 pivotPermutation2722; decide +kernel
  have hmoment : injectiveMoment H node2722 = injectiveMoment H pivotMatrix2722 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2722 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2722 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2722 (0 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2722 (0 : Fin 4) = raw6297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2722 raw6297; decide +kernel
    rw [heq]
    exact (canonical6297 hH).trans (sound979 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2722 (1 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2722 (1 : Fin 4) = raw7184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2722 raw7184; decide +kernel
    rw [heq]
    exact (canonical7184 hH).trans (sound1301 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2722 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2722 (2 : Fin 4) = raw7219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2722 raw7219; decide +kernel
    rw [heq]
    exact (canonical7219 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2722 (3 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2722 (3 : Fin 4) = raw7222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2722 raw7222; decide +kernel
    rw [heq]
    exact (canonical7222 hH).trans (sound1269 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2722 + (injectiveMoment H (mergeFirst pivotMatrix2722 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2722 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2722 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2722 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2722, value1267, value1269, value1301, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2723 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2723 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem sound2723 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2723 = Sparse.eval value2723 (momentVector H) := by
  have heq : pivotMatrix2723 = (fun u v => node2723 (pivotPermutation2723 u) v) := by apply Matrix.ext; unfold pivotMatrix2723 node2723 pivotPermutation2723; decide +kernel
  have hmoment : injectiveMoment H node2723 = injectiveMoment H pivotMatrix2723 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2723 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2723 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2723 (0 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2723 (0 : Fin 4) = raw6472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2723 raw6472; decide +kernel
    rw [heq]
    exact (canonical6472 hH).trans (sound786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2723 (1 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2723 (1 : Fin 4) = raw7172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2723 raw7172; decide +kernel
    rw [heq]
    exact (canonical7172 hH).trans (sound786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2723 (2 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2723 (2 : Fin 4) = raw7200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2723 raw7200; decide +kernel
    rw [heq]
    exact (canonical7200 hH).trans (sound1176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2723 (3 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2723 (3 : Fin 4) = raw7202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2723 raw7202; decide +kernel
    rw [heq]
    exact (canonical7202 hH).trans (sound771 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2723 + (injectiveMoment H (mergeFirst pivotMatrix2723 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2723 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2723 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2723 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2723, value1176, value771, value786, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2724 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2724 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2724 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2724 = Sparse.eval value2724 (momentVector H) := by
  have heq : pivotMatrix2724 = (fun u v => node2724 (pivotPermutation2724 u) v) := by apply Matrix.ext; unfold pivotMatrix2724 node2724 pivotPermutation2724; decide +kernel
  have hmoment : injectiveMoment H node2724 = injectiveMoment H pivotMatrix2724 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2724 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2724 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2724 (0 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2724 (0 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2724 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2724 (1 : Fin 4)) =
      Sparse.eval value1245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2724 (1 : Fin 4) = raw7177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2724 raw7177; decide +kernel
    rw [heq]
    exact (canonical7177 hH).trans (sound1245 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2724 (2 : Fin 4)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2724 (2 : Fin 4) = raw7207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2724 raw7207; decide +kernel
    rw [heq]
    exact (canonical7207 hH).trans (sound61 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2724 (3 : Fin 4)) =
      Sparse.eval value1262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2724 (3 : Fin 4) = raw7210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2724 raw7210; decide +kernel
    rw [heq]
    exact (canonical7210 hH).trans (sound1262 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2724 + (injectiveMoment H (mergeFirst pivotMatrix2724 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2724 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2724 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2724 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2724, value1048, value1245, value1262, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2725 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2725 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound2725 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2725 = Sparse.eval value2725 (momentVector H) := by
  have heq : pivotMatrix2725 = (fun u v => node2725 (pivotPermutation2725 u) v) := by apply Matrix.ext; unfold pivotMatrix2725 node2725 pivotPermutation2725; decide +kernel
  have hmoment : injectiveMoment H node2725 = injectiveMoment H pivotMatrix2725 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2725 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2725 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2725 (0 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2725 (0 : Fin 4) = raw6488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2725 raw6488; decide +kernel
    rw [heq]
    exact (canonical6488 hH).trans (sound1048 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2725 (1 : Fin 4)) =
      Sparse.eval value1246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2725 (1 : Fin 4) = raw7178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2725 raw7178; decide +kernel
    rw [heq]
    exact (canonical7178 hH).trans (sound1246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2725 (2 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2725 (2 : Fin 4) = raw7209 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2725 raw7209; decide +kernel
    rw [heq]
    exact (canonical7209 hH).trans (sound287 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2725 (3 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2725 (3 : Fin 4) = raw7211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2725 raw7211; decide +kernel
    rw [heq]
    exact (canonical7211 hH).trans (sound1048 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2725 + (injectiveMoment H (mergeFirst pivotMatrix2725 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2725 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2725 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2725 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2725, value1048, value1246, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2726 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2726 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem sound2726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2726 = Sparse.eval value2726 (momentVector H) := by
  have heq : pivotMatrix2726 = (fun u v => node2726 (pivotPermutation2726 u) v) := by apply Matrix.ext; unfold pivotMatrix2726 node2726 pivotPermutation2726; decide +kernel
  have hmoment : injectiveMoment H node2726 = injectiveMoment H pivotMatrix2726 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2726 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2726 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2726 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (0 : Fin 4) = raw6530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw6530; decide +kernel
    rw [heq]
    exact (canonical6530 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2726 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (1 : Fin 4) = raw7199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw7199; decide +kernel
    rw [heq]
    exact (canonical7199 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2726 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (2 : Fin 4) = raw7225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw7225; decide +kernel
    rw [heq]
    exact (canonical7225 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2726 (3 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (3 : Fin 4) = raw7228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw7228; decide +kernel
    rw [heq]
    exact (canonical7228 hH).trans (sound1277 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2726 + (injectiveMoment H (mergeFirst pivotMatrix2726 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2726 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2726 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2726 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2726, value1079, value1202, value1267, value1277, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2727 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2727 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem sound2727 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2727 = Sparse.eval value2727 (momentVector H) := by
  have heq : pivotMatrix2727 = (fun u v => node2727 (pivotPermutation2727 u) v) := by apply Matrix.ext; unfold pivotMatrix2727 node2727 pivotPermutation2727; decide +kernel
  have hmoment : injectiveMoment H node2727 = injectiveMoment H pivotMatrix2727 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2727 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2727 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2727 (0 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2727 (0 : Fin 4) = raw6538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2727 raw6538; decide +kernel
    rw [heq]
    exact (canonical6538 hH).trans (sound1081 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2727 (1 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2727 (1 : Fin 4) = raw7205 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2727 raw7205; decide +kernel
    rw [heq]
    exact (canonical7205 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2727 (2 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2727 (2 : Fin 4) = raw7232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2727 raw7232; decide +kernel
    rw [heq]
    exact (canonical7232 hH).trans (sound1268 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2727 (3 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2727 (3 : Fin 4) = raw7237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2727 raw7237; decide +kernel
    rw [heq]
    exact (canonical7237 hH).trans (sound1003 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2727 + (injectiveMoment H (mergeFirst pivotMatrix2727 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2727 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2727 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2727 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2727, value1003, value1081, value1268, value181, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2728 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2728 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem sound2728 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2728 = Sparse.eval value2728 (momentVector H) := by
  have heq : pivotMatrix2728 = (fun u v => node2728 (pivotPermutation2728 u) v) := by apply Matrix.ext; unfold pivotMatrix2728 node2728 pivotPermutation2728; decide +kernel
  have hmoment : injectiveMoment H node2728 = injectiveMoment H pivotMatrix2728 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2728 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2728 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2728 (0 : Fin 4)) =
      Sparse.eval value1214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2728 (0 : Fin 4) = raw7088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2728 raw7088; decide +kernel
    rw [heq]
    exact (canonical7088 hH).trans (sound1214 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2728 (1 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2728 (1 : Fin 4) = raw7180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2728 raw7180; decide +kernel
    rw [heq]
    exact (canonical7180 hH).trans (sound1009 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2728 (2 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2728 (2 : Fin 4) = raw7184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2728 raw7184; decide +kernel
    rw [heq]
    exact (canonical7184 hH).trans (sound1301 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2728 (3 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2728 (3 : Fin 4) = raw7185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2728 raw7185; decide +kernel
    rw [heq]
    exact (canonical7185 hH).trans (sound1249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2728 + (injectiveMoment H (mergeFirst pivotMatrix2728 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2728 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2728 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2728 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2728, value1009, value1214, value1249, value1301, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2729 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2729 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem sound2729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2729 = Sparse.eval value2729 (momentVector H) := by
  have heq : pivotMatrix2729 = (fun u v => node2729 (pivotPermutation2729 u) v) := by apply Matrix.ext; unfold pivotMatrix2729 node2729 pivotPermutation2729; decide +kernel
  have hmoment : injectiveMoment H node2729 = injectiveMoment H pivotMatrix2729 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2729 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2729 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2729 (0 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2729 (0 : Fin 4) = raw7844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2729 raw7844; decide +kernel
    rw [heq]
    exact (canonical7844 hH).trans (sound1083 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2729 (1 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2729 (1 : Fin 4) = raw7226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2729 raw7226; decide +kernel
    rw [heq]
    exact (canonical7226 hH).trans (sound1050 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2729 (2 : Fin 4)) =
      Sparse.eval value1255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2729 (2 : Fin 4) = raw7190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2729 raw7190; decide +kernel
    rw [heq]
    exact (canonical7190 hH).trans (sound1255 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2729 (3 : Fin 4)) =
      Sparse.eval value1252 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2729 (3 : Fin 4) = raw7188 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2729 raw7188; decide +kernel
    rw [heq]
    exact (canonical7188 hH).trans (sound1252 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2729 + (injectiveMoment H (mergeFirst pivotMatrix2729 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2729 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2729 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2729 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2729, value1050, value1083, value1252, value1255, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2730 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2730 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem sound2730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2730 = Sparse.eval value2730 (momentVector H) := by
  have heq : pivotMatrix2730 = (fun u v => node2730 (pivotPermutation2730 u) v) := by apply Matrix.ext; unfold pivotMatrix2730 node2730 pivotPermutation2730; decide +kernel
  have hmoment : injectiveMoment H node2730 = injectiveMoment H pivotMatrix2730 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2730 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2730 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2730 (0 : Fin 4)) =
      Sparse.eval value1225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2730 (0 : Fin 4) = raw7107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2730 raw7107; decide +kernel
    rw [heq]
    exact (canonical7107 hH).trans (sound1225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2730 (1 : Fin 4)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2730 (1 : Fin 4) = raw7215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2730 raw7215; decide +kernel
    rw [heq]
    exact (canonical7215 hH).trans (sound1264 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2730 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2730 (2 : Fin 4) = raw7219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2730 raw7219; decide +kernel
    rw [heq]
    exact (canonical7219 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2730 (3 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2730 (3 : Fin 4) = raw7221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2730 raw7221; decide +kernel
    rw [heq]
    exact (canonical7221 hH).trans (sound1268 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2730 + (injectiveMoment H (mergeFirst pivotMatrix2730 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2730 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2730 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2730 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2730, value1225, value1264, value1267, value1268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2731 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2731 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem sound2731 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2731 = Sparse.eval value2731 (momentVector H) := by
  have heq : pivotMatrix2731 = (fun u v => node2731 (pivotPermutation2731 u) v) := by apply Matrix.ext; unfold pivotMatrix2731 node2731 pivotPermutation2731; decide +kernel
  have hmoment : injectiveMoment H node2731 = injectiveMoment H pivotMatrix2731 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2731 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2731 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2731 (0 : Fin 4)) =
      Sparse.eval value1046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2731 (0 : Fin 4) = raw7111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2731 raw7111; decide +kernel
    rw [heq]
    exact (canonical7111 hH).trans (sound1046 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2731 (1 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2731 (1 : Fin 4) = raw7226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2731 raw7226; decide +kernel
    rw [heq]
    exact (canonical7226 hH).trans (sound1050 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2731 (2 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2731 (2 : Fin 4) = raw7233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2731 raw7233; decide +kernel
    rw [heq]
    exact (canonical7233 hH).trans (sound959 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2731 (3 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2731 (3 : Fin 4) = raw7235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2731 raw7235; decide +kernel
    rw [heq]
    exact (canonical7235 hH).trans (sound1047 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2731 + (injectiveMoment H (mergeFirst pivotMatrix2731 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2731 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2731 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2731 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2731, value1046, value1047, value1050, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2732 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2732 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem sound2732 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2732 = Sparse.eval value2732 (momentVector H) := by
  have heq : pivotMatrix2732 = (fun u v => node2732 (pivotPermutation2732 u) v) := by apply Matrix.ext; unfold pivotMatrix2732 node2732 pivotPermutation2732; decide +kernel
  have hmoment : injectiveMoment H node2732 = injectiveMoment H pivotMatrix2732 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2732 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2732 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2732 (0 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2732 (0 : Fin 4) = raw7112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2732 raw7112; decide +kernel
    rw [heq]
    exact (canonical7112 hH).trans (sound1231 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2732 (1 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2732 (1 : Fin 4) = raw7228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2732 raw7228; decide +kernel
    rw [heq]
    exact (canonical7228 hH).trans (sound1277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2732 (2 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2732 (2 : Fin 4) = raw7236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2732 raw7236; decide +kernel
    rw [heq]
    exact (canonical7236 hH).trans (sound1000 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2732 (3 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2732 (3 : Fin 4) = raw7237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2732 raw7237; decide +kernel
    rw [heq]
    exact (canonical7237 hH).trans (sound1003 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2732 + (injectiveMoment H (mergeFirst pivotMatrix2732 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2732 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2732 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2732 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2732, value1000, value1003, value1231, value1277, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2733 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2733 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem sound2733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2733 = Sparse.eval value2733 (momentVector H) := by
  have heq : pivotMatrix2733 = (fun u v => node2733 (pivotPermutation2733 u) v) := by apply Matrix.ext; unfold pivotMatrix2733 node2733 pivotPermutation2733; decide +kernel
  have hmoment : injectiveMoment H node2733 = injectiveMoment H pivotMatrix2733 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2733 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2733 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2733 (0 : Fin 4)) =
      Sparse.eval value1232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2733 (0 : Fin 4) = raw7113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2733 raw7113; decide +kernel
    rw [heq]
    exact (canonical7113 hH).trans (sound1232 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2733 (1 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2733 (1 : Fin 4) = raw7229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2733 raw7229; decide +kernel
    rw [heq]
    exact (canonical7229 hH).trans (sound1278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2733 (2 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2733 (2 : Fin 4) = raw7237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2733 raw7237; decide +kernel
    rw [heq]
    exact (canonical7237 hH).trans (sound1003 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2733 (3 : Fin 4)) =
      Sparse.eval value940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2733 (3 : Fin 4) = raw7238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2733 raw7238; decide +kernel
    rw [heq]
    exact (canonical7238 hH).trans (sound940 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2733 + (injectiveMoment H (mergeFirst pivotMatrix2733 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2733 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2733 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2733 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2733, value1003, value1232, value1278, value940, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2734 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2734 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem sound2734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2734 = Sparse.eval value2734 (momentVector H) := by
  have heq : pivotMatrix2734 = (fun u v => node2734 (pivotPermutation2734 u) v) := by apply Matrix.ext; unfold pivotMatrix2734 node2734 pivotPermutation2734; decide +kernel
  have hmoment : injectiveMoment H node2734 = injectiveMoment H pivotMatrix2734 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2734 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2734 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2734 (0 : Fin 4)) =
      Sparse.eval value1280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2734 (0 : Fin 4) = raw7349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2734 raw7349; decide +kernel
    rw [heq]
    exact (canonical7349 hH).trans (sound1280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2734 (1 : Fin 4)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2734 (1 : Fin 4) = raw7215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2734 raw7215; decide +kernel
    rw [heq]
    exact (canonical7215 hH).trans (sound1264 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2734 (2 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2734 (2 : Fin 4) = raw7211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2734 raw7211; decide +kernel
    rw [heq]
    exact (canonical7211 hH).trans (sound1048 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2734 (3 : Fin 4)) =
      Sparse.eval value1262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2734 (3 : Fin 4) = raw7210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2734 raw7210; decide +kernel
    rw [heq]
    exact (canonical7210 hH).trans (sound1262 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2734 + (injectiveMoment H (mergeFirst pivotMatrix2734 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2734 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2734 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2734 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2734, value1048, value1262, value1264, value1280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2735 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2735 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem sound2735 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2735 = Sparse.eval value2735 (momentVector H) := by
  have heq : pivotMatrix2735 = (fun u v => node2735 (pivotPermutation2735 u) v) := by apply Matrix.ext; unfold pivotMatrix2735 node2735 pivotPermutation2735; decide +kernel
  have hmoment : injectiveMoment H node2735 = injectiveMoment H pivotMatrix2735 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2735 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2735 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2735 (0 : Fin 4)) =
      Sparse.eval value1231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2735 (0 : Fin 4) = raw7825 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2735 raw7825; decide +kernel
    rw [heq]
    exact (canonical7825 hH).trans (sound1231 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2735 (1 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2735 (1 : Fin 4) = raw7244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2735 raw7244; decide +kernel
    rw [heq]
    exact (canonical7244 hH).trans (sound1003 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2735 (2 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2735 (2 : Fin 4) = raw7222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2735 raw7222; decide +kernel
    rw [heq]
    exact (canonical7222 hH).trans (sound1269 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2735 (3 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2735 (3 : Fin 4) = raw7221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2735 raw7221; decide +kernel
    rw [heq]
    exact (canonical7221 hH).trans (sound1268 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2735 + (injectiveMoment H (mergeFirst pivotMatrix2735 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2735 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2735 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2735 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2735, value1003, value1231, value1268, value1269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2736 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2736 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem sound2736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2736 = Sparse.eval value2736 (momentVector H) := by
  have heq : pivotMatrix2736 = (fun u v => node2736 (pivotPermutation2736 u) v) := by apply Matrix.ext; unfold pivotMatrix2736 node2736 pivotPermutation2736; decide +kernel
  have hmoment : injectiveMoment H node2736 = injectiveMoment H pivotMatrix2736 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2736 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2736 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2736 (0 : Fin 4)) =
      Sparse.eval value890 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2736 (0 : Fin 4) = raw5565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2736 raw5565; decide +kernel
    rw [heq]
    exact (canonical5565 hH).trans (sound890 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2736 (1 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2736 (1 : Fin 4) = raw8009 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2736 raw8009; decide +kernel
    rw [heq]
    exact (canonical8009 hH).trans (sound1178 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2736 (2 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2736 (2 : Fin 4) = raw8015 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2736 raw8015; decide +kernel
    rw [heq]
    exact (canonical8015 hH).trans (sound914 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2736 (3 : Fin 4)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2736 (3 : Fin 4) = raw8019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2736 raw8019; decide +kernel
    rw [heq]
    exact (canonical8019 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2736 + (injectiveMoment H (mergeFirst pivotMatrix2736 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2736 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2736 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2736 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2736, value1178, value52, value890, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2737 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2737 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2737 = Sparse.eval value2737 (momentVector H) := by
  have heq : pivotMatrix2737 = (fun u v => node2737 (pivotPermutation2737 u) v) := by apply Matrix.ext; unfold pivotMatrix2737 node2737 pivotPermutation2737; decide +kernel
  have hmoment : injectiveMoment H node2737 = injectiveMoment H pivotMatrix2737 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2737 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2737 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2737 (0 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2737 (0 : Fin 4) = raw5602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2737 raw5602; decide +kernel
    rw [heq]
    exact (canonical5602 hH).trans (sound1177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2737 (1 : Fin 4)) =
      Sparse.eval value1345 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2737 (1 : Fin 4) = raw8026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2737 raw8026; decide +kernel
    rw [heq]
    exact (canonical8026 hH).trans (sound1345 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2737 (2 : Fin 4)) =
      Sparse.eval value1220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2737 (2 : Fin 4) = raw8037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2737 raw8037; decide +kernel
    rw [heq]
    exact (canonical8037 hH).trans (sound1220 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2737 (3 : Fin 4)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2737 (3 : Fin 4) = raw8042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2737 raw8042; decide +kernel
    rw [heq]
    exact (canonical8042 hH).trans (sound168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2737 + (injectiveMoment H (mergeFirst pivotMatrix2737 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2737 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2737 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2737 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2737, value1177, value1220, value1345, value168, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2738 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound2738 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2738 = Sparse.eval value2738 (momentVector H) := by
  have heq : pivotMatrix2738 = (fun u v => node2738 (pivotPermutation2738 u) v) := by apply Matrix.ext; unfold pivotMatrix2738 node2738 pivotPermutation2738; decide +kernel
  have hmoment : injectiveMoment H node2738 = injectiveMoment H pivotMatrix2738 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2738 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2738 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2738 (0 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2738 (0 : Fin 4) = raw5623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2738 raw5623; decide +kernel
    rw [heq]
    exact (canonical5623 hH).trans (sound1171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2738 (1 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2738 (1 : Fin 4) = raw8031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2738 raw8031; decide +kernel
    rw [heq]
    exact (canonical8031 hH).trans (sound1094 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2738 (2 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2738 (2 : Fin 4) = raw8049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2738 raw8049; decide +kernel
    rw [heq]
    exact (canonical8049 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2738 (3 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2738 (3 : Fin 4) = raw8050 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2738 raw8050; decide +kernel
    rw [heq]
    exact (canonical8050 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2738 + (injectiveMoment H (mergeFirst pivotMatrix2738 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2738 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2738 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2738 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2738, value1094, value1171, value1207, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2739 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2739 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2739 = Sparse.eval value2739 (momentVector H) := by
  have heq : pivotMatrix2739 = (fun u v => node2739 (pivotPermutation2739 u) v) := by apply Matrix.ext; unfold pivotMatrix2739 node2739 pivotPermutation2739; decide +kernel
  have hmoment : injectiveMoment H node2739 = injectiveMoment H pivotMatrix2739 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2739 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2739 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2739 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2739 (0 : Fin 4) = raw5663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2739 raw5663; decide +kernel
    rw [heq]
    exact (canonical5663 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2739 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2739 (1 : Fin 4) = raw8056 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2739 raw8056; decide +kernel
    rw [heq]
    exact (canonical8056 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2739 (2 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2739 (2 : Fin 4) = raw8071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2739 raw8071; decide +kernel
    rw [heq]
    exact (canonical8071 hH).trans (sound1032 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2739 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2739 (3 : Fin 4) = raw8082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2739 raw8082; decide +kernel
    rw [heq]
    exact (canonical8082 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2739 + (injectiveMoment H (mergeFirst pivotMatrix2739 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2739 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2739 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2739 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2739, value1031, value1032, value1037, value145, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2740 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem sound2740 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2740 = Sparse.eval value2740 (momentVector H) := by
  have heq : pivotMatrix2740 = (fun u v => node2740 (pivotPermutation2740 u) v) := by apply Matrix.ext; unfold pivotMatrix2740 node2740 pivotPermutation2740; decide +kernel
  have hmoment : injectiveMoment H node2740 = injectiveMoment H pivotMatrix2740 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2740 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2740 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2740 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2740 (0 : Fin 4) = raw5710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2740 raw5710; decide +kernel
    rw [heq]
    exact (canonical5710 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2740 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2740 (1 : Fin 4) = raw8064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2740 raw8064; decide +kernel
    rw [heq]
    exact (canonical8064 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2740 (2 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2740 (2 : Fin 4) = raw8100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2740 raw8100; decide +kernel
    rw [heq]
    exact (canonical8100 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2740 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2740 (3 : Fin 4) = raw8102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2740 raw8102; decide +kernel
    rw [heq]
    exact (canonical8102 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2740 + (injectiveMoment H (mergeFirst pivotMatrix2740 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2740 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2740 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2740 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2740, value1053, value1063, value1079, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2741 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2741 = Sparse.eval value2741 (momentVector H) := by
  have heq : pivotMatrix2741 = (fun u v => node2741 (pivotPermutation2741 u) v) := by apply Matrix.ext; unfold pivotMatrix2741 node2741 pivotPermutation2741; decide +kernel
  have hmoment : injectiveMoment H node2741 = injectiveMoment H pivotMatrix2741 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2741 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2741 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2741 (0 : Fin 4)) =
      Sparse.eval value833 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2741 (0 : Fin 4) = raw5740 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2741 raw5740; decide +kernel
    rw [heq]
    exact (canonical5740 hH).trans (sound833 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2741 (1 : Fin 4)) =
      Sparse.eval value1189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2741 (1 : Fin 4) = raw8108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2741 raw8108; decide +kernel
    rw [heq]
    exact (canonical8108 hH).trans (sound1189 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2741 (2 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2741 (2 : Fin 4) = raw8119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2741 raw8119; decide +kernel
    rw [heq]
    exact (canonical8119 hH).trans (sound832 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2741 (3 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2741 (3 : Fin 4) = raw8121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2741 raw8121; decide +kernel
    rw [heq]
    exact (canonical8121 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2741 + (injectiveMoment H (mergeFirst pivotMatrix2741 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2741 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2741 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2741 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2741, value1189, value146, value832, value833, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2742 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2742 = Sparse.eval value2742 (momentVector H) := by
  have heq : pivotMatrix2742 = (fun u v => node2742 (pivotPermutation2742 u) v) := by apply Matrix.ext; unfold pivotMatrix2742 node2742 pivotPermutation2742; decide +kernel
  have hmoment : injectiveMoment H node2742 = injectiveMoment H pivotMatrix2742 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2742 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2742 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2742 (0 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2742 (0 : Fin 4) = raw5755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2742 raw5755; decide +kernel
    rw [heq]
    exact (canonical5755 hH).trans (sound1109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2742 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2742 (1 : Fin 4) = raw8112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2742 raw8112; decide +kernel
    rw [heq]
    exact (canonical8112 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2742 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2742 (2 : Fin 4) = raw8125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2742 raw8125; decide +kernel
    rw [heq]
    exact (canonical8125 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2742 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2742 (3 : Fin 4) = raw8139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2742 raw8139; decide +kernel
    rw [heq]
    exact (canonical8139 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2742 + (injectiveMoment H (mergeFirst pivotMatrix2742 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2742 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2742 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2742 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2742, value1079, value1109, value1110, value176, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2743 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound2743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2743 = Sparse.eval value2743 (momentVector H) := by
  have heq : pivotMatrix2743 = (fun u v => node2743 (pivotPermutation2743 u) v) := by apply Matrix.ext; unfold pivotMatrix2743 node2743 pivotPermutation2743; decide +kernel
  have hmoment : injectiveMoment H node2743 = injectiveMoment H pivotMatrix2743 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2743 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2743 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2743 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2743 (0 : Fin 4) = raw5768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2743 raw5768; decide +kernel
    rw [heq]
    exact (canonical5768 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2743 (1 : Fin 4)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2743 (1 : Fin 4) = raw8117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2743 raw8117; decide +kernel
    rw [heq]
    exact (canonical8117 hH).trans (sound1264 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2743 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2743 (2 : Fin 4) = raw8145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2743 raw8145; decide +kernel
    rw [heq]
    exact (canonical8145 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2743 (3 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2743 (3 : Fin 4) = raw8154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2743 raw8154; decide +kernel
    rw [heq]
    exact (canonical8154 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2743 + (injectiveMoment H (mergeFirst pivotMatrix2743 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2743 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2743 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2743 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2743, value1053, value1110, value1264, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2744 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2744 = Sparse.eval value2744 (momentVector H) := by
  have heq : pivotMatrix2744 = (fun u v => node2744 (pivotPermutation2744 u) v) := by apply Matrix.ext; unfold pivotMatrix2744 node2744 pivotPermutation2744; decide +kernel
  have hmoment : injectiveMoment H node2744 = injectiveMoment H pivotMatrix2744 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2744 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2744 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2744 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2744 (0 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2744 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2744 (1 : Fin 4)) =
      Sparse.eval value1126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2744 (1 : Fin 4) = raw8118 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2744 raw8118; decide +kernel
    rw [heq]
    exact (canonical8118 hH).trans (sound1126 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2744 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2744 (2 : Fin 4) = raw8158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2744 raw8158; decide +kernel
    rw [heq]
    exact (canonical8158 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2744 (3 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2744 (3 : Fin 4) = raw8159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2744 raw8159; decide +kernel
    rw [heq]
    exact (canonical8159 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2744 + (injectiveMoment H (mergeFirst pivotMatrix2744 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2744 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2744 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2744 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2744, value1110, value1117, value1126, value230, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2745 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem sound2745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2745 = Sparse.eval value2745 (momentVector H) := by
  have heq : pivotMatrix2745 = (fun u v => node2745 (pivotPermutation2745 u) v) := by apply Matrix.ext; unfold pivotMatrix2745 node2745 pivotPermutation2745; decide +kernel
  have hmoment : injectiveMoment H node2745 = injectiveMoment H pivotMatrix2745 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2745 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2745 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2745 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2745 (0 : Fin 4) = raw5832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2745 raw5832; decide +kernel
    rw [heq]
    exact (canonical5832 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2745 (1 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2745 (1 : Fin 4) = raw8242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2745 raw8242; decide +kernel
    rw [heq]
    exact (canonical8242 hH).trans (sound1057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2745 (2 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2745 (2 : Fin 4) = raw8251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2745 raw8251; decide +kernel
    rw [heq]
    exact (canonical8251 hH).trans (sound1054 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2745 (3 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2745 (3 : Fin 4) = raw8258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2745 raw8258; decide +kernel
    rw [heq]
    exact (canonical8258 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2745 + (injectiveMoment H (mergeFirst pivotMatrix2745 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2745 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2745 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2745 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2745, value1053, value1054, value1057, value207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2746 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2746 = Sparse.eval value2746 (momentVector H) := by
  have heq : pivotMatrix2746 = (fun u v => node2746 (pivotPermutation2746 u) v) := by apply Matrix.ext; unfold pivotMatrix2746 node2746 pivotPermutation2746; decide +kernel
  have hmoment : injectiveMoment H node2746 = injectiveMoment H pivotMatrix2746 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2746 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2746 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2746 (0 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (0 : Fin 4) = raw5994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw5994; decide +kernel
    rw [heq]
    exact (canonical5994 hH).trans (sound1063 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2746 (1 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (1 : Fin 4) = raw8269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw8269; decide +kernel
    rw [heq]
    exact (canonical8269 hH).trans (sound977 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2746 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (2 : Fin 4) = raw8270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw8270; decide +kernel
    rw [heq]
    exact (canonical8270 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2746 (3 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2746 (3 : Fin 4) = raw8271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2746 raw8271; decide +kernel
    rw [heq]
    exact (canonical8271 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2746 + (injectiveMoment H (mergeFirst pivotMatrix2746 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2746 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2746 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2746 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2746, value1063, value1267, value63, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2747 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem sound2747 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2747 = Sparse.eval value2747 (momentVector H) := by
  have heq : pivotMatrix2747 = (fun u v => node2747 (pivotPermutation2747 u) v) := by apply Matrix.ext; unfold pivotMatrix2747 node2747 pivotPermutation2747; decide +kernel
  have hmoment : injectiveMoment H node2747 = injectiveMoment H pivotMatrix2747 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2747 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2747 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2747 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2747 (0 : Fin 4) = raw6201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2747 raw6201; decide +kernel
    rw [heq]
    exact (canonical6201 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2747 (1 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2747 (1 : Fin 4) = raw8307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2747 raw8307; decide +kernel
    rw [heq]
    exact (canonical8307 hH).trans (sound998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2747 (2 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2747 (2 : Fin 4) = raw8312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2747 raw8312; decide +kernel
    rw [heq]
    exact (canonical8312 hH).trans (sound1198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2747 (3 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2747 (3 : Fin 4) = raw8313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2747 raw8313; decide +kernel
    rw [heq]
    exact (canonical8313 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2747 + (injectiveMoment H (mergeFirst pivotMatrix2747 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2747 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2747 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2747 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2747, value1168, value1198, value150, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2748 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2748 = Sparse.eval value2748 (momentVector H) := by
  have heq : pivotMatrix2748 = (fun u v => node2748 (pivotPermutation2748 u) v) := by apply Matrix.ext; unfold pivotMatrix2748 node2748 pivotPermutation2748; decide +kernel
  have hmoment : injectiveMoment H node2748 = injectiveMoment H pivotMatrix2748 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2748 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2748 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2748 (0 : Fin 4)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2748 (0 : Fin 4) = raw6212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2748 raw6212; decide +kernel
    rw [heq]
    exact (canonical6212 hH).trans (sound1268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2748 (1 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2748 (1 : Fin 4) = raw8308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2748 raw8308; decide +kernel
    rw [heq]
    exact (canonical8308 hH).trans (sound1099 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2748 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2748 (2 : Fin 4) = raw8314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2748 raw8314; decide +kernel
    rw [heq]
    exact (canonical8314 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2748 (3 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2748 (3 : Fin 4) = raw8315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2748 raw8315; decide +kernel
    rw [heq]
    exact (canonical8315 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2748 + (injectiveMoment H (mergeFirst pivotMatrix2748 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2748 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2748 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2748 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2748, value1099, value1265, value1268, value181, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2749 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem sound2749 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2749 = Sparse.eval value2749 (momentVector H) := by
  have heq : pivotMatrix2749 = (fun u v => node2749 (pivotPermutation2749 u) v) := by apply Matrix.ext; unfold pivotMatrix2749 node2749 pivotPermutation2749; decide +kernel
  have hmoment : injectiveMoment H node2749 = injectiveMoment H pivotMatrix2749 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2749 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2749 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2749 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2749 (0 : Fin 4) = raw6402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2749 raw6402; decide +kernel
    rw [heq]
    exact (canonical6402 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2749 (1 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2749 (1 : Fin 4) = raw8345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2749 raw8345; decide +kernel
    rw [heq]
    exact (canonical8345 hH).trans (sound771 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2749 (2 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2749 (2 : Fin 4) = raw8391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2749 raw8391; decide +kernel
    rw [heq]
    exact (canonical8391 hH).trans (sound959 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2749 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2749 (3 : Fin 4) = raw8397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2749 raw8397; decide +kernel
    rw [heq]
    exact (canonical8397 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2749 + (injectiveMoment H (mergeFirst pivotMatrix2749 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2749 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2749 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2749 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2749, value145, value771, value959, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2750 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem sound2750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2750 = Sparse.eval value2750 (momentVector H) := by
  have heq : pivotMatrix2750 = (fun u v => node2750 (pivotPermutation2750 u) v) := by apply Matrix.ext; unfold pivotMatrix2750 node2750 pivotPermutation2750; decide +kernel
  have hmoment : injectiveMoment H node2750 = injectiveMoment H pivotMatrix2750 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2750 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2750 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2750 (0 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2750 (0 : Fin 4) = raw6406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2750 raw6406; decide +kernel
    rw [heq]
    exact (canonical6406 hH).trans (sound1003 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2750 (1 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2750 (1 : Fin 4) = raw8349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2750 raw8349; decide +kernel
    rw [heq]
    exact (canonical8349 hH).trans (sound939 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2750 (2 : Fin 4)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2750 (2 : Fin 4) = raw8401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2750 raw8401; decide +kernel
    rw [heq]
    exact (canonical8401 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2750 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2750 (3 : Fin 4) = raw8410 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2750 raw8410; decide +kernel
    rw [heq]
    exact (canonical8410 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2750 + (injectiveMoment H (mergeFirst pivotMatrix2750 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2750 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2750 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2750 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2750, value1003, value1047, value185, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2751 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

theorem sound2751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2751 = Sparse.eval value2751 (momentVector H) := by
  have heq : pivotMatrix2751 = (fun u v => node2751 (pivotPermutation2751 u) v) := by apply Matrix.ext; unfold pivotMatrix2751 node2751 pivotPermutation2751; decide +kernel
  have hmoment : injectiveMoment H node2751 = injectiveMoment H pivotMatrix2751 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2751 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2751 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2751 (0 : Fin 4)) =
      Sparse.eval value1004 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2751 (0 : Fin 4) = raw6407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2751 raw6407; decide +kernel
    rw [heq]
    exact (canonical6407 hH).trans (sound1004 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2751 (1 : Fin 4)) =
      Sparse.eval value898 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2751 (1 : Fin 4) = raw8350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2751 raw8350; decide +kernel
    rw [heq]
    exact (canonical8350 hH).trans (sound898 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2751 (2 : Fin 4)) =
      Sparse.eval value1046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2751 (2 : Fin 4) = raw8402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2751 raw8402; decide +kernel
    rw [heq]
    exact (canonical8402 hH).trans (sound1046 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2751 (3 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2751 (3 : Fin 4) = raw8411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2751 raw8411; decide +kernel
    rw [heq]
    exact (canonical8411 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2751 + (injectiveMoment H (mergeFirst pivotMatrix2751 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2751 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2751 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2751 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2751, value1004, value1046, value155, value898, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
