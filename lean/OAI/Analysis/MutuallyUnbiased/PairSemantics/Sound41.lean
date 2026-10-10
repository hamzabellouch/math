import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical207
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical210
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2624 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2624 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem sound2624 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2624 = Sparse.eval value2624 (momentVector H) := by
  have heq : pivotMatrix2624 = (fun u v => node2624 (pivotPermutation2624 u) v) := by apply Matrix.ext; unfold pivotMatrix2624 node2624 pivotPermutation2624; decide +kernel
  have hmoment : injectiveMoment H node2624 = injectiveMoment H pivotMatrix2624 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2624 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2624 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2624 (0 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2624 (0 : Fin 4) = raw7287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2624 raw7287; decide +kernel
    rw [heq]
    exact (canonical7287 hH).trans (sound1203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2624 (1 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2624 (1 : Fin 4) = raw6633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2624 raw6633; decide +kernel
    rw [heq]
    exact (canonical6633 hH).trans (sound1109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2624 (2 : Fin 4)) =
      Sparse.eval value1098 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2624 (2 : Fin 4) = raw6610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2624 raw6610; decide +kernel
    rw [heq]
    exact (canonical6610 hH).trans (sound1098 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2624 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2624 (3 : Fin 4) = raw6608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2624 raw6608; decide +kernel
    rw [heq]
    exact (canonical6608 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2624 + (injectiveMoment H (mergeFirst pivotMatrix2624 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2624 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2624 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2624 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2624, value1098, value1109, value1203, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2625 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2625 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2625 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2625 = Sparse.eval value2625 (momentVector H) := by
  have heq : pivotMatrix2625 = (fun u v => node2625 (pivotPermutation2625 u) v) := by apply Matrix.ext; unfold pivotMatrix2625 node2625 pivotPermutation2625; decide +kernel
  have hmoment : injectiveMoment H node2625 = injectiveMoment H pivotMatrix2625 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2625 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2625 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2625 (0 : Fin 4)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2625 (0 : Fin 4) = raw7288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2625 raw7288; decide +kernel
    rw [heq]
    exact (canonical7288 hH).trans (sound1039 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2625 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2625 (1 : Fin 4) = raw6635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2625 raw6635; decide +kernel
    rw [heq]
    exact (canonical6635 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2625 (2 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2625 (2 : Fin 4) = raw6612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2625 raw6612; decide +kernel
    rw [heq]
    exact (canonical6612 hH).trans (sound1265 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2625 (3 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2625 (3 : Fin 4) = raw6609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2625 raw6609; decide +kernel
    rw [heq]
    exact (canonical6609 hH).trans (sound1096 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2625 + (injectiveMoment H (mergeFirst pivotMatrix2625 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2625 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2625 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2625 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2625, value1039, value1096, value1110, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2626 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2626 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem sound2626 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2626 = Sparse.eval value2626 (momentVector H) := by
  have heq : pivotMatrix2626 = (fun u v => node2626 (pivotPermutation2626 u) v) := by apply Matrix.ext; unfold pivotMatrix2626 node2626 pivotPermutation2626; decide +kernel
  have hmoment : injectiveMoment H node2626 = injectiveMoment H pivotMatrix2626 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2626 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2626 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2626 (0 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2626 (0 : Fin 4) = raw5739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2626 raw5739; decide +kernel
    rw [heq]
    exact (canonical5739 hH).trans (sound832 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2626 (1 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2626 (1 : Fin 4) = raw6600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2626 raw6600; decide +kernel
    rw [heq]
    exact (canonical6600 hH).trans (sound1094 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2626 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2626 (2 : Fin 4) = raw6635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2626 raw6635; decide +kernel
    rw [heq]
    exact (canonical6635 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2626 (3 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2626 (3 : Fin 4) = raw6638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2626 raw6638; decide +kernel
    rw [heq]
    exact (canonical6638 hH).trans (sound1079 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2626 + (injectiveMoment H (mergeFirst pivotMatrix2626 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2626 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2626 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2626 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2626, value1079, value1094, value1110, value832, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2627 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2627 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem sound2627 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2627 = Sparse.eval value2627 (momentVector H) := by
  have heq : pivotMatrix2627 = (fun u v => node2627 (pivotPermutation2627 u) v) := by apply Matrix.ext; unfold pivotMatrix2627 node2627 pivotPermutation2627; decide +kernel
  have hmoment : injectiveMoment H node2627 = injectiveMoment H pivotMatrix2627 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2627 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2627 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2627 (0 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2627 (0 : Fin 4) = raw5755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2627 raw5755; decide +kernel
    rw [heq]
    exact (canonical5755 hH).trans (sound1109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2627 (1 : Fin 4)) =
      Sparse.eval value1099 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2627 (1 : Fin 4) = raw6613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2627 raw6613; decide +kernel
    rw [heq]
    exact (canonical6613 hH).trans (sound1099 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2627 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2627 (2 : Fin 4) = raw6660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2627 raw6660; decide +kernel
    rw [heq]
    exact (canonical6660 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2627 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2627 (3 : Fin 4) = raw6662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2627 raw6662; decide +kernel
    rw [heq]
    exact (canonical6662 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2627 + (injectiveMoment H (mergeFirst pivotMatrix2627 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2627 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2627 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2627 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2627, value1099, value1109, value1117, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2628 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2628 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem sound2628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2628 = Sparse.eval value2628 (momentVector H) := by
  have heq : pivotMatrix2628 = (fun u v => node2628 (pivotPermutation2628 u) v) := by apply Matrix.ext; unfold pivotMatrix2628 node2628 pivotPermutation2628; decide +kernel
  have hmoment : injectiveMoment H node2628 = injectiveMoment H pivotMatrix2628 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2628 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2628 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2628 (0 : Fin 4)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2628 (0 : Fin 4) = raw5765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2628 raw5765; decide +kernel
    rw [heq]
    exact (canonical5765 hH).trans (sound1260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2628 (1 : Fin 4)) =
      Sparse.eval value1349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2628 (1 : Fin 4) = raw6621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2628 raw6621; decide +kernel
    rw [heq]
    exact (canonical6621 hH).trans (sound1349 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2628 (2 : Fin 4)) =
      Sparse.eval value1114 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2628 (2 : Fin 4) = raw6668 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2628 raw6668; decide +kernel
    rw [heq]
    exact (canonical6668 hH).trans (sound1114 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2628 (3 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2628 (3 : Fin 4) = raw6673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2628 raw6673; decide +kernel
    rw [heq]
    exact (canonical6673 hH).trans (sound1118 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2628 + (injectiveMoment H (mergeFirst pivotMatrix2628 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2628 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2628 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2628 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2628, value1114, value1118, value1260, value1349, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2629 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2629 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound2629 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2629 = Sparse.eval value2629 (momentVector H) := by
  have heq : pivotMatrix2629 = (fun u v => node2629 (pivotPermutation2629 u) v) := by apply Matrix.ext; unfold pivotMatrix2629 node2629 pivotPermutation2629; decide +kernel
  have hmoment : injectiveMoment H node2629 = injectiveMoment H pivotMatrix2629 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2629 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2629 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2629 (0 : Fin 4)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2629 (0 : Fin 4) = raw5768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2629 raw5768; decide +kernel
    rw [heq]
    exact (canonical5768 hH).trans (sound1053 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2629 (1 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2629 (1 : Fin 4) = raw6624 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2629 raw6624; decide +kernel
    rw [heq]
    exact (canonical6624 hH).trans (sound1241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2629 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2629 (2 : Fin 4) = raw6670 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2629 raw6670; decide +kernel
    rw [heq]
    exact (canonical6670 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2629 (3 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2629 (3 : Fin 4) = raw6676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2629 raw6676; decide +kernel
    rw [heq]
    exact (canonical6676 hH).trans (sound1242 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2629 + (injectiveMoment H (mergeFirst pivotMatrix2629 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2629 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2629 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2629 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2629, value1053, value1117, value1241, value1242, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2630 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2630 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound2630 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2630 = Sparse.eval value2630 (momentVector H) := by
  have heq : pivotMatrix2630 = (fun u v => node2630 (pivotPermutation2630 u) v) := by apply Matrix.ext; unfold pivotMatrix2630 node2630 pivotPermutation2630; decide +kernel
  have hmoment : injectiveMoment H node2630 = injectiveMoment H pivotMatrix2630 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2630 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2630 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2630 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2630 (0 : Fin 4) = raw5769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2630 raw5769; decide +kernel
    rw [heq]
    exact (canonical5769 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2630 (1 : Fin 4)) =
      Sparse.eval value1262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2630 (1 : Fin 4) = raw6625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2630 raw6625; decide +kernel
    rw [heq]
    exact (canonical6625 hH).trans (sound1262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2630 (2 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2630 (2 : Fin 4) = raw6673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2630 raw6673; decide +kernel
    rw [heq]
    exact (canonical6673 hH).trans (sound1118 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2630 (3 : Fin 4)) =
      Sparse.eval value1119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2630 (3 : Fin 4) = raw6677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2630 raw6677; decide +kernel
    rw [heq]
    exact (canonical6677 hH).trans (sound1119 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2630 + (injectiveMoment H (mergeFirst pivotMatrix2630 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2630 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2630 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2630 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2630, value1118, value1119, value1262, value1265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2631 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2631 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2631 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2631 = Sparse.eval value2631 (momentVector H) := by
  have heq : pivotMatrix2631 = (fun u v => node2631 (pivotPermutation2631 u) v) := by apply Matrix.ext; unfold pivotMatrix2631 node2631 pivotPermutation2631; decide +kernel
  have hmoment : injectiveMoment H node2631 = injectiveMoment H pivotMatrix2631 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2631 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2631 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2631 (0 : Fin 4)) =
      Sparse.eval value846 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2631 (0 : Fin 4) = raw5778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2631 raw5778; decide +kernel
    rw [heq]
    exact (canonical5778 hH).trans (sound846 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2631 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2631 (1 : Fin 4) = raw6635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2631 raw6635; decide +kernel
    rw [heq]
    exact (canonical6635 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2631 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2631 (2 : Fin 4) = raw6689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2631 raw6689; decide +kernel
    rw [heq]
    exact (canonical6689 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2631 (3 : Fin 4)) =
      Sparse.eval value1126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2631 (3 : Fin 4) = raw6691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2631 raw6691; decide +kernel
    rw [heq]
    exact (canonical6691 hH).trans (sound1126 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2631 + (injectiveMoment H (mergeFirst pivotMatrix2631 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2631 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2631 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2631 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2631, value1110, value1117, value1126, value846, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2632 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2632 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2632 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2632 = Sparse.eval value2632 (momentVector H) := by
  have heq : pivotMatrix2632 = (fun u v => node2632 (pivotPermutation2632 u) v) := by apply Matrix.ext; unfold pivotMatrix2632 node2632 pivotPermutation2632; decide +kernel
  have hmoment : injectiveMoment H node2632 = injectiveMoment H pivotMatrix2632 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2632 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2632 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2632 (0 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2632 (0 : Fin 4) = raw5784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2632 raw5784; decide +kernel
    rw [heq]
    exact (canonical5784 hH).trans (sound1110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2632 (1 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2632 (1 : Fin 4) = raw6660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2632 raw6660; decide +kernel
    rw [heq]
    exact (canonical6660 hH).trans (sound1117 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2632 (2 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2632 (2 : Fin 4) = raw6694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2632 raw6694; decide +kernel
    rw [heq]
    exact (canonical6694 hH).trans (sound1118 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2632 (3 : Fin 4)) =
      Sparse.eval value1119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2632 (3 : Fin 4) = raw6697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2632 raw6697; decide +kernel
    rw [heq]
    exact (canonical6697 hH).trans (sound1119 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2632 + (injectiveMoment H (mergeFirst pivotMatrix2632 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2632 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2632 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2632 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2632, value1110, value1117, value1118, value1119, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2633 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2633 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2633 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2633 = Sparse.eval value2633 (momentVector H) := by
  have heq : pivotMatrix2633 = (fun u v => node2633 (pivotPermutation2633 u) v) := by apply Matrix.ext; unfold pivotMatrix2633 node2633 pivotPermutation2633; decide +kernel
  have hmoment : injectiveMoment H node2633 = injectiveMoment H pivotMatrix2633 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2633 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2633 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2633 (0 : Fin 4)) =
      Sparse.eval value854 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2633 (0 : Fin 4) = raw5823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2633 raw5823; decide +kernel
    rw [heq]
    exact (canonical5823 hH).trans (sound854 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2633 (1 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2633 (1 : Fin 4) = raw6612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2633 raw6612; decide +kernel
    rw [heq]
    exact (canonical6612 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2633 (2 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2633 (2 : Fin 4) = raw6635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2633 raw6635; decide +kernel
    rw [heq]
    exact (canonical6635 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2633 (3 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2633 (3 : Fin 4) = raw6637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2633 raw6637; decide +kernel
    rw [heq]
    exact (canonical6637 hH).trans (sound1112 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2633 + (injectiveMoment H (mergeFirst pivotMatrix2633 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2633 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2633 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2633 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2633, value1110, value1112, value1265, value854, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2634 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2634 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem sound2634 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2634 = Sparse.eval value2634 (momentVector H) := by
  have heq : pivotMatrix2634 = (fun u v => node2634 (pivotPermutation2634 u) v) := by apply Matrix.ext; unfold pivotMatrix2634 node2634 pivotPermutation2634; decide +kernel
  have hmoment : injectiveMoment H node2634 = injectiveMoment H pivotMatrix2634 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2634 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2634 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2634 (0 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2634 (0 : Fin 4) = raw6436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2634 raw6436; decide +kernel
    rw [heq]
    exact (canonical6436 hH).trans (sound1037 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2634 (1 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2634 (1 : Fin 4) = raw6629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2634 raw6629; decide +kernel
    rw [heq]
    exact (canonical6629 hH).trans (sound1075 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2634 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2634 (2 : Fin 4) = raw6638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2634 raw6638; decide +kernel
    rw [heq]
    exact (canonical6638 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2634 (3 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2634 (3 : Fin 4) = raw6639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2634 raw6639; decide +kernel
    rw [heq]
    exact (canonical6639 hH).trans (sound1113 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2634 + (injectiveMoment H (mergeFirst pivotMatrix2634 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2634 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2634 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2634 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2634, value1037, value1075, value1079, value1113, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2635 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2635 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem sound2635 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2635 = Sparse.eval value2635 (momentVector H) := by
  have heq : pivotMatrix2635 = (fun u v => node2635 (pivotPermutation2635 u) v) := by apply Matrix.ext; unfold pivotMatrix2635 node2635 pivotPermutation2635; decide +kernel
  have hmoment : injectiveMoment H node2635 = injectiveMoment H pivotMatrix2635 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2635 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2635 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2635 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2635 (0 : Fin 4) = raw6927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2635 raw6927; decide +kernel
    rw [heq]
    exact (canonical6927 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2635 (1 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2635 (1 : Fin 4) = raw6661 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2635 raw6661; decide +kernel
    rw [heq]
    exact (canonical6661 hH).trans (sound1242 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2635 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2635 (2 : Fin 4) = raw6638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2635 raw6638; decide +kernel
    rw [heq]
    exact (canonical6638 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2635 (3 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2635 (3 : Fin 4) = raw6637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2635 raw6637; decide +kernel
    rw [heq]
    exact (canonical6637 hH).trans (sound1112 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2635 + (injectiveMoment H (mergeFirst pivotMatrix2635 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2635 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2635 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2635 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2635, value1057, value1079, value1112, value1242, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2636 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2636 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem sound2636 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2636 = Sparse.eval value2636 (momentVector H) := by
  have heq : pivotMatrix2636 = (fun u v => node2636 (pivotPermutation2636 u) v) := by apply Matrix.ext; unfold pivotMatrix2636 node2636 pivotPermutation2636; decide +kernel
  have hmoment : injectiveMoment H node2636 = injectiveMoment H pivotMatrix2636 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2636 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2636 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2636 (0 : Fin 4)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2636 (0 : Fin 4) = raw7330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2636 raw7330; decide +kernel
    rw [heq]
    exact (canonical7330 hH).trans (sound1221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2636 (1 : Fin 4)) =
      Sparse.eval value1124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2636 (1 : Fin 4) = raw6687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2636 raw6687; decide +kernel
    rw [heq]
    exact (canonical6687 hH).trans (sound1124 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2636 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2636 (2 : Fin 4) = raw6638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2636 raw6638; decide +kernel
    rw [heq]
    exact (canonical6638 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2636 (3 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2636 (3 : Fin 4) = raw6636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2636 raw6636; decide +kernel
    rw [heq]
    exact (canonical6636 hH).trans (sound1109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2636 + (injectiveMoment H (mergeFirst pivotMatrix2636 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2636 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2636 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2636 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2636, value1079, value1109, value1124, value1221, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2637 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2637 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem sound2637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2637 = Sparse.eval value2637 (momentVector H) := by
  have heq : pivotMatrix2637 = (fun u v => node2637 (pivotPermutation2637 u) v) := by apply Matrix.ext; unfold pivotMatrix2637 node2637 pivotPermutation2637; decide +kernel
  have hmoment : injectiveMoment H node2637 = injectiveMoment H pivotMatrix2637 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2637 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2637 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2637 (0 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2637 (0 : Fin 4) = raw7498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2637 raw7498; decide +kernel
    rw [heq]
    exact (canonical7498 hH).trans (sound1242 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2637 (1 : Fin 4)) =
      Sparse.eval value1119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2637 (1 : Fin 4) = raw6690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2637 raw6690; decide +kernel
    rw [heq]
    exact (canonical6690 hH).trans (sound1119 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2637 (2 : Fin 4)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2637 (2 : Fin 4) = raw6637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2637 raw6637; decide +kernel
    rw [heq]
    exact (canonical6637 hH).trans (sound1112 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2637 (3 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2637 (3 : Fin 4) = raw6634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2637 raw6634; decide +kernel
    rw [heq]
    exact (canonical6634 hH).trans (sound1110 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2637 + (injectiveMoment H (mergeFirst pivotMatrix2637 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2637 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2637 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2637 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2637, value1110, value1112, value1119, value1242, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2638 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2638 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem sound2638 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2638 = Sparse.eval value2638 (momentVector H) := by
  have heq : pivotMatrix2638 = (fun u v => node2638 (pivotPermutation2638 u) v) := by apply Matrix.ext; unfold pivotMatrix2638 node2638 pivotPermutation2638; decide +kernel
  have hmoment : injectiveMoment H node2638 = injectiveMoment H pivotMatrix2638 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2638 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2638 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2638 (0 : Fin 4)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2638 (0 : Fin 4) = raw6462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2638 raw6462; decide +kernel
    rw [heq]
    exact (canonical6462 hH).trans (sound1043 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2638 (1 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2638 (1 : Fin 4) = raw6633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2638 raw6633; decide +kernel
    rw [heq]
    exact (canonical6633 hH).trans (sound1109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2638 (2 : Fin 4)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2638 (2 : Fin 4) = raw6652 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2638 raw6652; decide +kernel
    rw [heq]
    exact (canonical6652 hH).trans (sound1116 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2638 (3 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2638 (3 : Fin 4) = raw6658 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2638 raw6658; decide +kernel
    rw [heq]
    exact (canonical6658 hH).trans (sound1117 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2638 + (injectiveMoment H (mergeFirst pivotMatrix2638 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2638 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2638 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2638 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2638, value1043, value1109, value1116, value1117, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2639 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2639 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound2639 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2639 = Sparse.eval value2639 (momentVector H) := by
  have heq : pivotMatrix2639 = (fun u v => node2639 (pivotPermutation2639 u) v) := by apply Matrix.ext; unfold pivotMatrix2639 node2639 pivotPermutation2639; decide +kernel
  have hmoment : injectiveMoment H node2639 = injectiveMoment H pivotMatrix2639 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2639 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2639 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2639 (0 : Fin 4)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2639 (0 : Fin 4) = raw6465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2639 raw6465; decide +kernel
    rw [heq]
    exact (canonical6465 hH).trans (sound1044 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2639 (1 : Fin 4)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2639 (1 : Fin 4) = raw6634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2639 raw6634; decide +kernel
    rw [heq]
    exact (canonical6634 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2639 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2639 (2 : Fin 4) = raw6658 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2639 raw6658; decide +kernel
    rw [heq]
    exact (canonical6658 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2639 (3 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2639 (3 : Fin 4) = raw6659 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2639 raw6659; decide +kernel
    rw [heq]
    exact (canonical6659 hH).trans (sound1118 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2639 + (injectiveMoment H (mergeFirst pivotMatrix2639 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2639 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2639 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2639 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2639, value1044, value1110, value1117, value1118, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2640 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2640 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem sound2640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2640 = Sparse.eval value2640 (momentVector H) := by
  have heq : pivotMatrix2640 = (fun u v => node2640 (pivotPermutation2640 u) v) := by apply Matrix.ext; unfold pivotMatrix2640 node2640 pivotPermutation2640; decide +kernel
  have hmoment : injectiveMoment H node2640 = injectiveMoment H pivotMatrix2640 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2640 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2640 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2640 (0 : Fin 4)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2640 (0 : Fin 4) = raw6471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2640 raw6471; decide +kernel
    rw [heq]
    exact (canonical6471 hH).trans (sound1203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2640 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2640 (1 : Fin 4) = raw6638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2640 raw6638; decide +kernel
    rw [heq]
    exact (canonical6638 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2640 (2 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2640 (2 : Fin 4) = raw6661 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2640 raw6661; decide +kernel
    rw [heq]
    exact (canonical6661 hH).trans (sound1242 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2640 (3 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2640 (3 : Fin 4) = raw6662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2640 raw6662; decide +kernel
    rw [heq]
    exact (canonical6662 hH).trans (sound936 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2640 + (injectiveMoment H (mergeFirst pivotMatrix2640 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2640 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2640 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2640 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2640, value1079, value1203, value1242, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2641 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2641 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem sound2641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2641 = Sparse.eval value2641 (momentVector H) := by
  have heq : pivotMatrix2641 = (fun u v => node2641 (pivotPermutation2641 u) v) := by apply Matrix.ext; unfold pivotMatrix2641 node2641 pivotPermutation2641; decide +kernel
  have hmoment : injectiveMoment H node2641 = injectiveMoment H pivotMatrix2641 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2641 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2641 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2641 (0 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2641 (0 : Fin 4) = raw6472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2641 raw6472; decide +kernel
    rw [heq]
    exact (canonical6472 hH).trans (sound786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2641 (1 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2641 (1 : Fin 4) = raw6639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2641 raw6639; decide +kernel
    rw [heq]
    exact (canonical6639 hH).trans (sound1113 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2641 (2 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2641 (2 : Fin 4) = raw6662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2641 raw6662; decide +kernel
    rw [heq]
    exact (canonical6662 hH).trans (sound936 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2641 (3 : Fin 4)) =
      Sparse.eval value921 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2641 (3 : Fin 4) = raw6663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2641 raw6663; decide +kernel
    rw [heq]
    exact (canonical6663 hH).trans (sound921 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2641 + (injectiveMoment H (mergeFirst pivotMatrix2641 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2641 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2641 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2641 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2641, value1113, value786, value921, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2642 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2642 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem sound2642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2642 = Sparse.eval value2642 (momentVector H) := by
  have heq : pivotMatrix2642 = (fun u v => node2642 (pivotPermutation2642 u) v) := by apply Matrix.ext; unfold pivotMatrix2642 node2642 pivotPermutation2642; decide +kernel
  have hmoment : injectiveMoment H node2642 = injectiveMoment H pivotMatrix2642 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2642 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2642 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2642 (0 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2642 (0 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2642 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2642 (1 : Fin 4)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2642 (1 : Fin 4) = raw6664 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2642 raw6664; decide +kernel
    rw [heq]
    exact (canonical6664 hH).trans (sound293 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2642 (2 : Fin 4)) =
      Sparse.eval value1117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2642 (2 : Fin 4) = raw6670 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2642 raw6670; decide +kernel
    rw [heq]
    exact (canonical6670 hH).trans (sound1117 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2642 (3 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2642 (3 : Fin 4) = raw6673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2642 raw6673; decide +kernel
    rw [heq]
    exact (canonical6673 hH).trans (sound1118 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2642 + (injectiveMoment H (mergeFirst pivotMatrix2642 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2642 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2642 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2642 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2642, value1048, value1117, value1118, value293, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2643 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2643 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem sound2643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2643 = Sparse.eval value2643 (momentVector H) := by
  have heq : pivotMatrix2643 = (fun u v => node2643 (pivotPermutation2643 u) v) := by apply Matrix.ext; unfold pivotMatrix2643 node2643 pivotPermutation2643; decide +kernel
  have hmoment : injectiveMoment H node2643 = injectiveMoment H pivotMatrix2643 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2643 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2643 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2643 (0 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2643 (0 : Fin 4) = raw6492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2643 raw6492; decide +kernel
    rw [heq]
    exact (canonical6492 hH).trans (sound1265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2643 (1 : Fin 4)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2643 (1 : Fin 4) = raw6665 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2643 raw6665; decide +kernel
    rw [heq]
    exact (canonical6665 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2643 (2 : Fin 4)) =
      Sparse.eval value1119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2643 (2 : Fin 4) = raw6677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2643 raw6677; decide +kernel
    rw [heq]
    exact (canonical6677 hH).trans (sound1119 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2643 (3 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2643 (3 : Fin 4) = raw6678 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2643 raw6678; decide +kernel
    rw [heq]
    exact (canonical6678 hH).trans (sound837 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2643 + (injectiveMoment H (mergeFirst pivotMatrix2643 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2643 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2643 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2643 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2643, value1119, value1265, value227, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2644 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2644 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem sound2644 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2644 = Sparse.eval value2644 (momentVector H) := by
  have heq : pivotMatrix2644 = (fun u v => node2644 (pivotPermutation2644 u) v) := by apply Matrix.ext; unfold pivotMatrix2644 node2644 pivotPermutation2644; decide +kernel
  have hmoment : injectiveMoment H node2644 = injectiveMoment H pivotMatrix2644 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2644 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2644 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2644 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2644 (0 : Fin 4) = raw6530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2644 raw6530; decide +kernel
    rw [heq]
    exact (canonical6530 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2644 (1 : Fin 4)) =
      Sparse.eval value1124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2644 (1 : Fin 4) = raw6687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2644 raw6687; decide +kernel
    rw [heq]
    exact (canonical6687 hH).trans (sound1124 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2644 (2 : Fin 4)) =
      Sparse.eval value1126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2644 (2 : Fin 4) = raw6691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2644 raw6691; decide +kernel
    rw [heq]
    exact (canonical6691 hH).trans (sound1126 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2644 (3 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2644 (3 : Fin 4) = raw6692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2644 raw6692; decide +kernel
    rw [heq]
    exact (canonical6692 hH).trans (sound1123 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2644 + (injectiveMoment H (mergeFirst pivotMatrix2644 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2644 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2644 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2644 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2644, value1079, value1123, value1124, value1126, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2645 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2645 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem sound2645 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2645 = Sparse.eval value2645 (momentVector H) := by
  have heq : pivotMatrix2645 = (fun u v => node2645 (pivotPermutation2645 u) v) := by apply Matrix.ext; unfold pivotMatrix2645 node2645 pivotPermutation2645; decide +kernel
  have hmoment : injectiveMoment H node2645 = injectiveMoment H pivotMatrix2645 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2645 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2645 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2645 (0 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2645 (0 : Fin 4) = raw6537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2645 raw6537; decide +kernel
    rw [heq]
    exact (canonical6537 hH).trans (sound1242 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2645 (1 : Fin 4)) =
      Sparse.eval value1126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2645 (1 : Fin 4) = raw6691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2645 raw6691; decide +kernel
    rw [heq]
    exact (canonical6691 hH).trans (sound1126 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2645 (2 : Fin 4)) =
      Sparse.eval value1118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2645 (2 : Fin 4) = raw6696 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2645 raw6696; decide +kernel
    rw [heq]
    exact (canonical6696 hH).trans (sound1118 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2645 (3 : Fin 4)) =
      Sparse.eval value1119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2645 (3 : Fin 4) = raw6697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2645 raw6697; decide +kernel
    rw [heq]
    exact (canonical6697 hH).trans (sound1119 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2645 + (injectiveMoment H (mergeFirst pivotMatrix2645 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2645 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2645 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2645 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2645, value1118, value1119, value1126, value1242, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2646 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2646 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem sound2646 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2646 = Sparse.eval value2646 (momentVector H) := by
  have heq : pivotMatrix2646 = (fun u v => node2646 (pivotPermutation2646 u) v) := by apply Matrix.ext; unfold pivotMatrix2646 node2646 pivotPermutation2646; decide +kernel
  have hmoment : injectiveMoment H node2646 = injectiveMoment H pivotMatrix2646 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2646 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2646 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2646 (0 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2646 (0 : Fin 4) = raw6538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2646 raw6538; decide +kernel
    rw [heq]
    exact (canonical6538 hH).trans (sound1081 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2646 (1 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2646 (1 : Fin 4) = raw6692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2646 raw6692; decide +kernel
    rw [heq]
    exact (canonical6692 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2646 (2 : Fin 4)) =
      Sparse.eval value1119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2646 (2 : Fin 4) = raw6697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2646 raw6697; decide +kernel
    rw [heq]
    exact (canonical6697 hH).trans (sound1119 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2646 (3 : Fin 4)) =
      Sparse.eval value1122 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2646 (3 : Fin 4) = raw6698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2646 raw6698; decide +kernel
    rw [heq]
    exact (canonical6698 hH).trans (sound1122 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2646 + (injectiveMoment H (mergeFirst pivotMatrix2646 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2646 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2646 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2646 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2646, value1081, value1119, value1122, value1123, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2647 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2647 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem sound2647 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2647 = Sparse.eval value2647 (momentVector H) := by
  have heq : pivotMatrix2647 = (fun u v => node2647 (pivotPermutation2647 u) v) := by apply Matrix.ext; unfold pivotMatrix2647 node2647 pivotPermutation2647; decide +kernel
  have hmoment : injectiveMoment H node2647 = injectiveMoment H pivotMatrix2647 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2647 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2647 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2647 (0 : Fin 4)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2647 (0 : Fin 4) = raw6933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2647 raw6933; decide +kernel
    rw [heq]
    exact (canonical6933 hH).trans (sound1040 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2647 (1 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2647 (1 : Fin 4) = raw6703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2647 raw6703; decide +kernel
    rw [heq]
    exact (canonical6703 hH).trans (sound835 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2647 (2 : Fin 4)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2647 (2 : Fin 4) = raw6701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2647 raw6701; decide +kernel
    rw [heq]
    exact (canonical6701 hH).trans (sound835 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2647 (3 : Fin 4)) =
      Sparse.eval value1114 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2647 (3 : Fin 4) = raw6700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2647 raw6700; decide +kernel
    rw [heq]
    exact (canonical6700 hH).trans (sound1114 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2647 + (injectiveMoment H (mergeFirst pivotMatrix2647 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2647 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2647 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2647 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2647, value1040, value1114, value835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2648 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound2648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2648 = Sparse.eval value2648 (momentVector H) := by
  have heq : pivotMatrix2648 = (fun u v => node2648 (pivotPermutation2648 u) v) := by apply Matrix.ext; unfold pivotMatrix2648 node2648 pivotPermutation2648; decide +kernel
  have hmoment : injectiveMoment H node2648 = injectiveMoment H pivotMatrix2648 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2648 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2648 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2648 (0 : Fin 5)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2648 (0 : Fin 5) = raw5856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2648 raw5856; decide +kernel
    rw [heq]
    exact (canonical5856 hH).trans (sound858 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2648 (1 : Fin 5)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2648 (1 : Fin 5) = raw6719 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2648 raw6719; decide +kernel
    rw [heq]
    exact (canonical6719 hH).trans (sound858 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2648 (2 : Fin 5)) =
      Sparse.eval value1130 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2648 (2 : Fin 5) = raw6723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2648 raw6723; decide +kernel
    rw [heq]
    exact (canonical6723 hH).trans (sound1130 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2648 (3 : Fin 5)) =
      Sparse.eval value1131 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2648 (3 : Fin 5) = raw6725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2648 raw6725; decide +kernel
    rw [heq]
    exact (canonical6725 hH).trans (sound1131 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2648 (4 : Fin 5)) =
      Sparse.eval value654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2648 (4 : Fin 5) = raw6726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2648 raw6726; decide +kernel
    rw [heq]
    exact (canonical6726 hH).trans (sound654 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2648 + (injectiveMoment H (mergeFirst pivotMatrix2648 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2648 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2648 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2648 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2648 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2648, value1130, value1131, value654, value858, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2649 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound2649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2649 = Sparse.eval value2649 (momentVector H) := by
  have heq : pivotMatrix2649 = (fun u v => node2649 (pivotPermutation2649 u) v) := by apply Matrix.ext; unfold pivotMatrix2649 node2649 pivotPermutation2649; decide +kernel
  have hmoment : injectiveMoment H node2649 = injectiveMoment H pivotMatrix2649 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2649 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2649 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2649 (0 : Fin 5)) =
      Sparse.eval value860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2649 (0 : Fin 5) = raw5859 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2649 raw5859; decide +kernel
    rw [heq]
    exact (canonical5859 hH).trans (sound860 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2649 (1 : Fin 5)) =
      Sparse.eval value860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2649 (1 : Fin 5) = raw6720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2649 raw6720; decide +kernel
    rw [heq]
    exact (canonical6720 hH).trans (sound860 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2649 (2 : Fin 5)) =
      Sparse.eval value654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2649 (2 : Fin 5) = raw6726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2649 raw6726; decide +kernel
    rw [heq]
    exact (canonical6726 hH).trans (sound654 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2649 (3 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2649 (3 : Fin 5) = raw6728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2649 raw6728; decide +kernel
    rw [heq]
    exact (canonical6728 hH).trans (sound1132 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2649 (4 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2649 (4 : Fin 5) = raw6729 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2649 raw6729; decide +kernel
    rw [heq]
    exact (canonical6729 hH).trans (sound1132 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2649 + (injectiveMoment H (mergeFirst pivotMatrix2649 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2649 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2649 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2649 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2649 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2649, value1132, value654, value860, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2650 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem sound2650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2650 = Sparse.eval value2650 (momentVector H) := by
  have heq : pivotMatrix2650 = (fun u v => node2650 (pivotPermutation2650 u) v) := by apply Matrix.ext; unfold pivotMatrix2650 node2650 pivotPermutation2650; decide +kernel
  have hmoment : injectiveMoment H node2650 = injectiveMoment H pivotMatrix2650 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2650 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2650 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2650 (0 : Fin 5)) =
      Sparse.eval value861 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2650 (0 : Fin 5) = raw5861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2650 raw5861; decide +kernel
    rw [heq]
    exact (canonical5861 hH).trans (sound861 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2650 (1 : Fin 5)) =
      Sparse.eval value861 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2650 (1 : Fin 5) = raw6721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2650 raw6721; decide +kernel
    rw [heq]
    exact (canonical6721 hH).trans (sound861 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2650 (2 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2650 (2 : Fin 5) = raw6728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2650 raw6728; decide +kernel
    rw [heq]
    exact (canonical6728 hH).trans (sound1132 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2650 (3 : Fin 5)) =
      Sparse.eval value1133 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2650 (3 : Fin 5) = raw6731 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2650 raw6731; decide +kernel
    rw [heq]
    exact (canonical6731 hH).trans (sound1133 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2650 (4 : Fin 5)) =
      Sparse.eval value1134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2650 (4 : Fin 5) = raw6732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2650 raw6732; decide +kernel
    rw [heq]
    exact (canonical6732 hH).trans (sound1134 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2650 + (injectiveMoment H (mergeFirst pivotMatrix2650 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2650 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2650 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2650 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2650 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2650, value1132, value1133, value1134, value861, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2651 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2651 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2651 = Sparse.eval value2651 (momentVector H) := by
  have heq : pivotMatrix2651 = (fun u v => node2651 (pivotPermutation2651 u) v) := by apply Matrix.ext; unfold pivotMatrix2651 node2651 pivotPermutation2651; decide +kernel
  have hmoment : injectiveMoment H node2651 = injectiveMoment H pivotMatrix2651 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2651 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2651 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2651 (0 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2651 (0 : Fin 5) = raw7372 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2651 raw7372; decide +kernel
    rw [heq]
    exact (canonical7372 hH).trans (sound1151 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2651 (1 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2651 (1 : Fin 5) = raw6740 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2651 raw6740; decide +kernel
    rw [heq]
    exact (canonical6740 hH).trans (sound1151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2651 (2 : Fin 5)) =
      Sparse.eval value654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2651 (2 : Fin 5) = raw6726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2651 raw6726; decide +kernel
    rw [heq]
    exact (canonical6726 hH).trans (sound654 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2651 (3 : Fin 5)) =
      Sparse.eval value1130 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2651 (3 : Fin 5) = raw6724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2651 raw6724; decide +kernel
    rw [heq]
    exact (canonical6724 hH).trans (sound1130 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2651 (4 : Fin 5)) =
      Sparse.eval value1130 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2651 (4 : Fin 5) = raw6723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2651 raw6723; decide +kernel
    rw [heq]
    exact (canonical6723 hH).trans (sound1130 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2651 + (injectiveMoment H (mergeFirst pivotMatrix2651 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2651 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2651 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2651 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2651 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2651, value1130, value1151, value654, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2652 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2652 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2652 = Sparse.eval value2652 (momentVector H) := by
  have heq : pivotMatrix2652 = (fun u v => node2652 (pivotPermutation2652 u) v) := by apply Matrix.ext; unfold pivotMatrix2652 node2652 pivotPermutation2652; decide +kernel
  have hmoment : injectiveMoment H node2652 = injectiveMoment H pivotMatrix2652 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2652 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2652 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2652 (0 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2652 (0 : Fin 5) = raw7373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2652 raw7373; decide +kernel
    rw [heq]
    exact (canonical7373 hH).trans (sound659 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2652 (1 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2652 (1 : Fin 5) = raw6741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2652 raw6741; decide +kernel
    rw [heq]
    exact (canonical6741 hH).trans (sound659 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2652 (2 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2652 (2 : Fin 5) = raw6728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2652 raw6728; decide +kernel
    rw [heq]
    exact (canonical6728 hH).trans (sound1132 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2652 (3 : Fin 5)) =
      Sparse.eval value654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2652 (3 : Fin 5) = raw6726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2652 raw6726; decide +kernel
    rw [heq]
    exact (canonical6726 hH).trans (sound654 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2652 (4 : Fin 5)) =
      Sparse.eval value1131 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2652 (4 : Fin 5) = raw6725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2652 raw6725; decide +kernel
    rw [heq]
    exact (canonical6725 hH).trans (sound1131 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2652 + (injectiveMoment H (mergeFirst pivotMatrix2652 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2652 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2652 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2652 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2652 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2652, value1131, value1132, value654, value659, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2653 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound2653 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2653 = Sparse.eval value2653 (momentVector H) := by
  have heq : pivotMatrix2653 = (fun u v => node2653 (pivotPermutation2653 u) v) := by apply Matrix.ext; unfold pivotMatrix2653 node2653 pivotPermutation2653; decide +kernel
  have hmoment : injectiveMoment H node2653 = injectiveMoment H pivotMatrix2653 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2653 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2653 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2653 (0 : Fin 5)) =
      Sparse.eval value547 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2653 (0 : Fin 5) = raw2717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2653 raw2717; decide +kernel
    rw [heq]
    exact (canonical2717 hH).trans (sound547 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2653 (1 : Fin 5)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2653 (1 : Fin 5) = raw6719 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2653 raw6719; decide +kernel
    rw [heq]
    exact (canonical6719 hH).trans (sound858 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2653 (2 : Fin 5)) =
      Sparse.eval value1136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2653 (2 : Fin 5) = raw6774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2653 raw6774; decide +kernel
    rw [heq]
    exact (canonical6774 hH).trans (sound1136 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2653 (3 : Fin 5)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2653 (3 : Fin 5) = raw6780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2653 raw6780; decide +kernel
    rw [heq]
    exact (canonical6780 hH).trans (sound279 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2653 (4 : Fin 5)) =
      Sparse.eval value1147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2653 (4 : Fin 5) = raw6782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2653 raw6782; decide +kernel
    rw [heq]
    exact (canonical6782 hH).trans (sound1147 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2653 + (injectiveMoment H (mergeFirst pivotMatrix2653 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2653 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2653 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2653 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2653 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2653, value1136, value1147, value279, value547, value858, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2654 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound2654 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2654 = Sparse.eval value2654 (momentVector H) := by
  have heq : pivotMatrix2654 = (fun u v => node2654 (pivotPermutation2654 u) v) := by apply Matrix.ext; unfold pivotMatrix2654 node2654 pivotPermutation2654; decide +kernel
  have hmoment : injectiveMoment H node2654 = injectiveMoment H pivotMatrix2654 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2654 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2654 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2654 (0 : Fin 5)) =
      Sparse.eval value549 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2654 (0 : Fin 5) = raw2720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2654 raw2720; decide +kernel
    rw [heq]
    exact (canonical2720 hH).trans (sound549 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2654 (1 : Fin 5)) =
      Sparse.eval value860 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2654 (1 : Fin 5) = raw6720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2654 raw6720; decide +kernel
    rw [heq]
    exact (canonical6720 hH).trans (sound860 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2654 (2 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2654 (2 : Fin 5) = raw6775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2654 raw6775; decide +kernel
    rw [heq]
    exact (canonical6775 hH).trans (sound1143 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2654 (3 : Fin 5)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2654 (3 : Fin 5) = raw6784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2654 raw6784; decide +kernel
    rw [heq]
    exact (canonical6784 hH).trans (sound280 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2654 (4 : Fin 5)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2654 (4 : Fin 5) = raw6787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2654 raw6787; decide +kernel
    rw [heq]
    exact (canonical6787 hH).trans (sound280 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2654 + (injectiveMoment H (mergeFirst pivotMatrix2654 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2654 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2654 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2654 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2654 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2654, value1143, value280, value549, value860, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2655 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound2655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2655 = Sparse.eval value2655 (momentVector H) := by
  have heq : pivotMatrix2655 = (fun u v => node2655 (pivotPermutation2655 u) v) := by apply Matrix.ext; unfold pivotMatrix2655 node2655 pivotPermutation2655; decide +kernel
  have hmoment : injectiveMoment H node2655 = injectiveMoment H pivotMatrix2655 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2655 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2655 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2655 (0 : Fin 5)) =
      Sparse.eval value560 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2655 (0 : Fin 5) = raw2748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2655 raw2748; decide +kernel
    rw [heq]
    exact (canonical2748 hH).trans (sound560 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2655 (1 : Fin 5)) =
      Sparse.eval value1130 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2655 (1 : Fin 5) = raw6723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2655 raw6723; decide +kernel
    rw [heq]
    exact (canonical6723 hH).trans (sound1130 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2655 (2 : Fin 5)) =
      Sparse.eval value1135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2655 (2 : Fin 5) = raw6791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2655 raw6791; decide +kernel
    rw [heq]
    exact (canonical6791 hH).trans (sound1135 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2655 (3 : Fin 5)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2655 (3 : Fin 5) = raw6806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2655 raw6806; decide +kernel
    rw [heq]
    exact (canonical6806 hH).trans (sound283 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2655 (4 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2655 (4 : Fin 5) = raw6813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2655 raw6813; decide +kernel
    rw [heq]
    exact (canonical6813 hH).trans (sound1151 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2655 + (injectiveMoment H (mergeFirst pivotMatrix2655 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2655 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2655 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2655 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2655 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2655, value1130, value1135, value1151, value283, value560, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2656 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound2656 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2656 = Sparse.eval value2656 (momentVector H) := by
  have heq : pivotMatrix2656 = (fun u v => node2656 (pivotPermutation2656 u) v) := by apply Matrix.ext; unfold pivotMatrix2656 node2656 pivotPermutation2656; decide +kernel
  have hmoment : injectiveMoment H node2656 = injectiveMoment H pivotMatrix2656 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2656 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2656 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2656 (0 : Fin 5)) =
      Sparse.eval value561 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2656 (0 : Fin 5) = raw2753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2656 raw2753; decide +kernel
    rw [heq]
    exact (canonical2753 hH).trans (sound561 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2656 (1 : Fin 5)) =
      Sparse.eval value1131 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2656 (1 : Fin 5) = raw6725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2656 raw6725; decide +kernel
    rw [heq]
    exact (canonical6725 hH).trans (sound1131 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2656 (2 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2656 (2 : Fin 5) = raw6793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2656 raw6793; decide +kernel
    rw [heq]
    exact (canonical6793 hH).trans (sound1141 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2656 (3 : Fin 5)) =
      Sparse.eval value1146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2656 (3 : Fin 5) = raw6815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2656 raw6815; decide +kernel
    rw [heq]
    exact (canonical6815 hH).trans (sound1146 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2656 (4 : Fin 5)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2656 (4 : Fin 5) = raw6817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2656 raw6817; decide +kernel
    rw [heq]
    exact (canonical6817 hH).trans (sound1152 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2656 + (injectiveMoment H (mergeFirst pivotMatrix2656 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2656 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2656 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2656 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2656 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2656, value1131, value1141, value1146, value1152, value561, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2657 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound2657 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2657 = Sparse.eval value2657 (momentVector H) := by
  have heq : pivotMatrix2657 = (fun u v => node2657 (pivotPermutation2657 u) v) := by apply Matrix.ext; unfold pivotMatrix2657 node2657 pivotPermutation2657; decide +kernel
  have hmoment : injectiveMoment H node2657 = injectiveMoment H pivotMatrix2657 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2657 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2657 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2657 (0 : Fin 5)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2657 (0 : Fin 5) = raw2757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2657 raw2757; decide +kernel
    rw [heq]
    exact (canonical2757 hH).trans (sound563 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2657 (1 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2657 (1 : Fin 5) = raw6728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2657 raw6728; decide +kernel
    rw [heq]
    exact (canonical6728 hH).trans (sound1132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2657 (2 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2657 (2 : Fin 5) = raw6794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2657 raw6794; decide +kernel
    rw [heq]
    exact (canonical6794 hH).trans (sound872 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2657 (3 : Fin 5)) =
      Sparse.eval value1149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2657 (3 : Fin 5) = raw6819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2657 raw6819; decide +kernel
    rw [heq]
    exact (canonical6819 hH).trans (sound1149 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2657 (4 : Fin 5)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2657 (4 : Fin 5) = raw6821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2657 raw6821; decide +kernel
    rw [heq]
    exact (canonical6821 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2657 + (injectiveMoment H (mergeFirst pivotMatrix2657 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2657 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2657 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2657 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2657 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2657, value1132, value1149, value285, value563, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2658 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem sound2658 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2658 = Sparse.eval value2658 (momentVector H) := by
  have heq : pivotMatrix2658 = (fun u v => node2658 (pivotPermutation2658 u) v) := by apply Matrix.ext; unfold pivotMatrix2658 node2658 pivotPermutation2658; decide +kernel
  have hmoment : injectiveMoment H node2658 = injectiveMoment H pivotMatrix2658 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2658 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2658 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2658 (0 : Fin 5)) =
      Sparse.eval value565 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2658 (0 : Fin 5) = raw2761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2658 raw2761; decide +kernel
    rw [heq]
    exact (canonical2761 hH).trans (sound565 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2658 (1 : Fin 5)) =
      Sparse.eval value1134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2658 (1 : Fin 5) = raw6732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2658 raw6732; decide +kernel
    rw [heq]
    exact (canonical6732 hH).trans (sound1134 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2658 (2 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2658 (2 : Fin 5) = raw6795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2658 raw6795; decide +kernel
    rw [heq]
    exact (canonical6795 hH).trans (sound742 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2658 (3 : Fin 5)) =
      Sparse.eval value1150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2658 (3 : Fin 5) = raw6822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2658 raw6822; decide +kernel
    rw [heq]
    exact (canonical6822 hH).trans (sound1150 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2658 (4 : Fin 5)) =
      Sparse.eval value1150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2658 (4 : Fin 5) = raw6824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2658 raw6824; decide +kernel
    rw [heq]
    exact (canonical6824 hH).trans (sound1150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2658 + (injectiveMoment H (mergeFirst pivotMatrix2658 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2658 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2658 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2658 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2658 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2658, value1134, value1150, value565, value742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2659 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound2659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2659 = Sparse.eval value2659 (momentVector H) := by
  have heq : pivotMatrix2659 = (fun u v => node2659 (pivotPermutation2659 u) v) := by apply Matrix.ext; unfold pivotMatrix2659 node2659 pivotPermutation2659; decide +kernel
  have hmoment : injectiveMoment H node2659 = injectiveMoment H pivotMatrix2659 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2659 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2659 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2659 (0 : Fin 5)) =
      Sparse.eval value569 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2659 (0 : Fin 5) = raw2799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2659 raw2799; decide +kernel
    rw [heq]
    exact (canonical2799 hH).trans (sound569 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2659 (1 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2659 (1 : Fin 5) = raw6743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2659 raw6743; decide +kernel
    rw [heq]
    exact (canonical6743 hH).trans (sound1141 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2659 (2 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2659 (2 : Fin 5) = raw6833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2659 raw6833; decide +kernel
    rw [heq]
    exact (canonical6833 hH).trans (sound1141 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2659 (3 : Fin 5)) =
      Sparse.eval value1146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2659 (3 : Fin 5) = raw6840 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2659 raw6840; decide +kernel
    rw [heq]
    exact (canonical6840 hH).trans (sound1146 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2659 (4 : Fin 5)) =
      Sparse.eval value1153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2659 (4 : Fin 5) = raw6844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2659 raw6844; decide +kernel
    rw [heq]
    exact (canonical6844 hH).trans (sound1153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2659 + (injectiveMoment H (mergeFirst pivotMatrix2659 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2659 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2659 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2659 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2659 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2659, value1141, value1146, value1153, value569, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2660 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2660 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2660 = Sparse.eval value2660 (momentVector H) := by
  have heq : pivotMatrix2660 = (fun u v => node2660 (pivotPermutation2660 u) v) := by apply Matrix.ext; unfold pivotMatrix2660 node2660 pivotPermutation2660; decide +kernel
  have hmoment : injectiveMoment H node2660 = injectiveMoment H pivotMatrix2660 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2660 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2660 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2660 (0 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2660 (0 : Fin 5) = raw2800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2660 raw2800; decide +kernel
    rw [heq]
    exact (canonical2800 hH).trans (sound570 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2660 (1 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2660 (1 : Fin 5) = raw6744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2660 raw6744; decide +kernel
    rw [heq]
    exact (canonical6744 hH).trans (sound711 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2660 (2 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2660 (2 : Fin 5) = raw6834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2660 raw6834; decide +kernel
    rw [heq]
    exact (canonical6834 hH).trans (sound711 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2660 (3 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2660 (3 : Fin 5) = raw6841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2660 raw6841; decide +kernel
    rw [heq]
    exact (canonical6841 hH).trans (sound1151 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2660 (4 : Fin 5)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2660 (4 : Fin 5) = raw6848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2660 raw6848; decide +kernel
    rw [heq]
    exact (canonical6848 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2660 + (injectiveMoment H (mergeFirst pivotMatrix2660 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2660 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2660 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2660 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2660 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2660, value1151, value287, value570, value711, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2661 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem sound2661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2661 = Sparse.eval value2661 (momentVector H) := by
  have heq : pivotMatrix2661 = (fun u v => node2661 (pivotPermutation2661 u) v) := by apply Matrix.ext; unfold pivotMatrix2661 node2661 pivotPermutation2661; decide +kernel
  have hmoment : injectiveMoment H node2661 = injectiveMoment H pivotMatrix2661 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2661 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2661 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2661 (0 : Fin 5)) =
      Sparse.eval value572 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2661 (0 : Fin 5) = raw2808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2661 raw2808; decide +kernel
    rw [heq]
    exact (canonical2808 hH).trans (sound572 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2661 (1 : Fin 5)) =
      Sparse.eval value1142 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2661 (1 : Fin 5) = raw6745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2661 raw6745; decide +kernel
    rw [heq]
    exact (canonical6745 hH).trans (sound1142 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2661 (2 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2661 (2 : Fin 5) = raw6835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2661 raw6835; decide +kernel
    rw [heq]
    exact (canonical6835 hH).trans (sound1141 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2661 (3 : Fin 5)) =
      Sparse.eval value1147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2661 (3 : Fin 5) = raw6850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2661 raw6850; decide +kernel
    rw [heq]
    exact (canonical6850 hH).trans (sound1147 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2661 (4 : Fin 5)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2661 (4 : Fin 5) = raw6853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2661 raw6853; decide +kernel
    rw [heq]
    exact (canonical6853 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2661 + (injectiveMoment H (mergeFirst pivotMatrix2661 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2661 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2661 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2661 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2661 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2661, value1141, value1142, value1147, value288, value572, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2662 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem sound2662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2662 = Sparse.eval value2662 (momentVector H) := by
  have heq : pivotMatrix2662 = (fun u v => node2662 (pivotPermutation2662 u) v) := by apply Matrix.ext; unfold pivotMatrix2662 node2662 pivotPermutation2662; decide +kernel
  have hmoment : injectiveMoment H node2662 = injectiveMoment H pivotMatrix2662 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2662 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2662 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2662 (0 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2662 (0 : Fin 5) = raw2809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2662 raw2809; decide +kernel
    rw [heq]
    exact (canonical2809 hH).trans (sound573 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2662 (1 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2662 (1 : Fin 5) = raw6746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2662 raw6746; decide +kernel
    rw [heq]
    exact (canonical6746 hH).trans (sound655 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2662 (2 : Fin 5)) =
      Sparse.eval value709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2662 (2 : Fin 5) = raw6836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2662 raw6836; decide +kernel
    rw [heq]
    exact (canonical6836 hH).trans (sound709 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2662 (3 : Fin 5)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2662 (3 : Fin 5) = raw6851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2662 raw6851; decide +kernel
    rw [heq]
    exact (canonical6851 hH).trans (sound1152 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2662 (4 : Fin 5)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2662 (4 : Fin 5) = raw6854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2662 raw6854; decide +kernel
    rw [heq]
    exact (canonical6854 hH).trans (sound1152 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2662 + (injectiveMoment H (mergeFirst pivotMatrix2662 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2662 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2662 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2662 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2662 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2662, value1152, value573, value655, value709, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2663 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2663 = Sparse.eval value2663 (momentVector H) := by
  have heq : pivotMatrix2663 = (fun u v => node2663 (pivotPermutation2663 u) v) := by apply Matrix.ext; unfold pivotMatrix2663 node2663 pivotPermutation2663; decide +kernel
  have hmoment : injectiveMoment H node2663 = injectiveMoment H pivotMatrix2663 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2663 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2663 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2663 (0 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2663 (0 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2663 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2663 (1 : Fin 5)) =
      Sparse.eval value654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2663 (1 : Fin 5) = raw6726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2663 raw6726; decide +kernel
    rw [heq]
    exact (canonical6726 hH).trans (sound654 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2663 (2 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2663 (2 : Fin 5) = raw6775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2663 raw6775; decide +kernel
    rw [heq]
    exact (canonical6775 hH).trans (sound1143 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2663 (3 : Fin 5)) =
      Sparse.eval value1147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2663 (3 : Fin 5) = raw6781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2663 raw6781; decide +kernel
    rw [heq]
    exact (canonical6781 hH).trans (sound1147 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2663 (4 : Fin 5)) =
      Sparse.eval value1147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2663 (4 : Fin 5) = raw6782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2663 raw6782; decide +kernel
    rw [heq]
    exact (canonical6782 hH).trans (sound1147 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2663 + (injectiveMoment H (mergeFirst pivotMatrix2663 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2663 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2663 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2663 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2663 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2663, value1143, value1147, value641, value654, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2664 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound2664 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2664 = Sparse.eval value2664 (momentVector H) := by
  have heq : pivotMatrix2664 = (fun u v => node2664 (pivotPermutation2664 u) v) := by apply Matrix.ext; unfold pivotMatrix2664 node2664 pivotPermutation2664; decide +kernel
  have hmoment : injectiveMoment H node2664 = injectiveMoment H pivotMatrix2664 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2664 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2664 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2664 (0 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2664 (0 : Fin 5) = raw4035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2664 raw4035; decide +kernel
    rw [heq]
    exact (canonical4035 hH).trans (sound648 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2664 (1 : Fin 5)) =
      Sparse.eval value1132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2664 (1 : Fin 5) = raw6728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2664 raw6728; decide +kernel
    rw [heq]
    exact (canonical6728 hH).trans (sound1132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2664 (2 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2664 (2 : Fin 5) = raw6776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2664 raw6776; decide +kernel
    rw [heq]
    exact (canonical6776 hH).trans (sound743 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2664 (3 : Fin 5)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2664 (3 : Fin 5) = raw6784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2664 raw6784; decide +kernel
    rw [heq]
    exact (canonical6784 hH).trans (sound280 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2664 (4 : Fin 5)) =
      Sparse.eval value1148 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2664 (4 : Fin 5) = raw6785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2664 raw6785; decide +kernel
    rw [heq]
    exact (canonical6785 hH).trans (sound1148 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2664 + (injectiveMoment H (mergeFirst pivotMatrix2664 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2664 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2664 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2664 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2664 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2664, value1132, value1148, value280, value648, value743, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2665 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2665 = Sparse.eval value2665 (momentVector H) := by
  have heq : pivotMatrix2665 = (fun u v => node2665 (pivotPermutation2665 u) v) := by apply Matrix.ext; unfold pivotMatrix2665 node2665 pivotPermutation2665; decide +kernel
  have hmoment : injectiveMoment H node2665 = injectiveMoment H pivotMatrix2665 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2665 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2665 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2665 (0 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2665 (0 : Fin 5) = raw4071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2665 raw4071; decide +kernel
    rw [heq]
    exact (canonical4071 hH).trans (sound659 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2665 (1 : Fin 5)) =
      Sparse.eval value1135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2665 (1 : Fin 5) = raw6739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2665 raw6739; decide +kernel
    rw [heq]
    exact (canonical6739 hH).trans (sound1135 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2665 (2 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2665 (2 : Fin 5) = raw6793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2665 raw6793; decide +kernel
    rw [heq]
    exact (canonical6793 hH).trans (sound1141 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2665 (3 : Fin 5)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2665 (3 : Fin 5) = raw6806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2665 raw6806; decide +kernel
    rw [heq]
    exact (canonical6806 hH).trans (sound283 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2665 (4 : Fin 5)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2665 (4 : Fin 5) = raw6810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2665 raw6810; decide +kernel
    rw [heq]
    exact (canonical6810 hH).trans (sound1152 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2665 + (injectiveMoment H (mergeFirst pivotMatrix2665 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2665 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2665 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2665 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2665 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2665, value1135, value1141, value1152, value283, value659, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2666 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2666 = Sparse.eval value2666 (momentVector H) := by
  have heq : pivotMatrix2666 = (fun u v => node2666 (pivotPermutation2666 u) v) := by apply Matrix.ext; unfold pivotMatrix2666 node2666 pivotPermutation2666; decide +kernel
  have hmoment : injectiveMoment H node2666 = injectiveMoment H pivotMatrix2666 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2666 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2666 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2666 (0 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2666 (0 : Fin 5) = raw4077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2666 raw4077; decide +kernel
    rw [heq]
    exact (canonical4077 hH).trans (sound661 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2666 (1 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2666 (1 : Fin 5) = raw6741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2666 raw6741; decide +kernel
    rw [heq]
    exact (canonical6741 hH).trans (sound659 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2666 (2 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2666 (2 : Fin 5) = raw6794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2666 raw6794; decide +kernel
    rw [heq]
    exact (canonical6794 hH).trans (sound872 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2666 (3 : Fin 5)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2666 (3 : Fin 5) = raw6816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2666 raw6816; decide +kernel
    rw [heq]
    exact (canonical6816 hH).trans (sound284 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2666 (4 : Fin 5)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2666 (4 : Fin 5) = raw6817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2666 raw6817; decide +kernel
    rw [heq]
    exact (canonical6817 hH).trans (sound1152 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2666 + (injectiveMoment H (mergeFirst pivotMatrix2666 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2666 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2666 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2666 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2666 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2666, value1152, value284, value659, value661, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2667 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem sound2667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2667 = Sparse.eval value2667 (momentVector H) := by
  have heq : pivotMatrix2667 = (fun u v => node2667 (pivotPermutation2667 u) v) := by apply Matrix.ext; unfold pivotMatrix2667 node2667 pivotPermutation2667; decide +kernel
  have hmoment : injectiveMoment H node2667 = injectiveMoment H pivotMatrix2667 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2667 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2667 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2667 (0 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2667 (0 : Fin 5) = raw4115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2667 raw4115; decide +kernel
    rw [heq]
    exact (canonical4115 hH).trans (sound667 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2667 (1 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2667 (1 : Fin 5) = raw6752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2667 raw6752; decide +kernel
    rw [heq]
    exact (canonical6752 hH).trans (sound1141 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2667 (2 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2667 (2 : Fin 5) = raw6835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2667 raw6835; decide +kernel
    rw [heq]
    exact (canonical6835 hH).trans (sound1141 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2667 (3 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2667 (3 : Fin 5) = raw6841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2667 raw6841; decide +kernel
    rw [heq]
    exact (canonical6841 hH).trans (sound1151 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2667 (4 : Fin 5)) =
      Sparse.eval value1153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2667 (4 : Fin 5) = raw6844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2667 raw6844; decide +kernel
    rw [heq]
    exact (canonical6844 hH).trans (sound1153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2667 + (injectiveMoment H (mergeFirst pivotMatrix2667 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2667 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2667 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2667 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2667 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2667, value1141, value1151, value1153, value667, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2668 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2668 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2668 = Sparse.eval value2668 (momentVector H) := by
  have heq : pivotMatrix2668 = (fun u v => node2668 (pivotPermutation2668 u) v) := by apply Matrix.ext; unfold pivotMatrix2668 node2668 pivotPermutation2668; decide +kernel
  have hmoment : injectiveMoment H node2668 = injectiveMoment H pivotMatrix2668 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2668 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2668 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2668 (0 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2668 (0 : Fin 5) = raw7399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2668 raw7399; decide +kernel
    rw [heq]
    exact (canonical7399 hH).trans (sound655 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2668 (1 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2668 (1 : Fin 5) = raw6758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2668 raw6758; decide +kernel
    rw [heq]
    exact (canonical6758 hH).trans (sound1143 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2668 (2 : Fin 5)) =
      Sparse.eval value709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2668 (2 : Fin 5) = raw6750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2668 raw6750; decide +kernel
    rw [heq]
    exact (canonical6750 hH).trans (sound709 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2668 (3 : Fin 5)) =
      Sparse.eval value1136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2668 (3 : Fin 5) = raw6749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2668 raw6749; decide +kernel
    rw [heq]
    exact (canonical6749 hH).trans (sound1136 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2668 (4 : Fin 5)) =
      Sparse.eval value1136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2668 (4 : Fin 5) = raw6748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2668 raw6748; decide +kernel
    rw [heq]
    exact (canonical6748 hH).trans (sound1136 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2668 + (injectiveMoment H (mergeFirst pivotMatrix2668 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2668 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2668 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2668 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2668 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2668, value1136, value1143, value655, value709, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2669 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2669 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2669 = Sparse.eval value2669 (momentVector H) := by
  have heq : pivotMatrix2669 = (fun u v => node2669 (pivotPermutation2669 u) v) := by apply Matrix.ext; unfold pivotMatrix2669 node2669 pivotPermutation2669; decide +kernel
  have hmoment : injectiveMoment H node2669 = injectiveMoment H pivotMatrix2669 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2669 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2669 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2669 (0 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2669 (0 : Fin 5) = raw5882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2669 raw5882; decide +kernel
    rw [heq]
    exact (canonical5882 hH).trans (sound872 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2669 (1 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2669 (1 : Fin 5) = raw6744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2669 raw6744; decide +kernel
    rw [heq]
    exact (canonical6744 hH).trans (sound711 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2669 (2 : Fin 5)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2669 (2 : Fin 5) = raw6751 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2669 raw6751; decide +kernel
    rw [heq]
    exact (canonical6751 hH).trans (sound230 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2669 (3 : Fin 5)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2669 (3 : Fin 5) = raw6752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2669 raw6752; decide +kernel
    rw [heq]
    exact (canonical6752 hH).trans (sound1141 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2669 (4 : Fin 5)) =
      Sparse.eval value709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2669 (4 : Fin 5) = raw6753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2669 raw6753; decide +kernel
    rw [heq]
    exact (canonical6753 hH).trans (sound709 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2669 + (injectiveMoment H (mergeFirst pivotMatrix2669 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2669 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2669 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2669 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2669 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2669, value1141, value230, value709, value711, value872, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2670 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

theorem sound2670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2670 = Sparse.eval value2670 (momentVector H) := by
  have heq : pivotMatrix2670 = (fun u v => node2670 (pivotPermutation2670 u) v) := by apply Matrix.ext; unfold pivotMatrix2670 node2670 pivotPermutation2670; decide +kernel
  have hmoment : injectiveMoment H node2670 = injectiveMoment H pivotMatrix2670 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2670 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2670 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2670 (0 : Fin 5)) =
      Sparse.eval value1287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2670 (0 : Fin 5) = raw7400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2670 raw7400; decide +kernel
    rw [heq]
    exact (canonical7400 hH).trans (sound1287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2670 (1 : Fin 5)) =
      Sparse.eval value1144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2670 (1 : Fin 5) = raw6765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2670 raw6765; decide +kernel
    rw [heq]
    exact (canonical6765 hH).trans (sound1144 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2670 (2 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2670 (2 : Fin 5) = raw6758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2670 raw6758; decide +kernel
    rw [heq]
    exact (canonical6758 hH).trans (sound1143 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2670 (3 : Fin 5)) =
      Sparse.eval value1137 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2670 (3 : Fin 5) = raw6757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2670 raw6757; decide +kernel
    rw [heq]
    exact (canonical6757 hH).trans (sound1137 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2670 (4 : Fin 5)) =
      Sparse.eval value1137 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2670 (4 : Fin 5) = raw6756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2670 raw6756; decide +kernel
    rw [heq]
    exact (canonical6756 hH).trans (sound1137 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2670 + (injectiveMoment H (mergeFirst pivotMatrix2670 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2670 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2670 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2670 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2670 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2670, value1137, value1143, value1144, value1287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2671 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2671 = Sparse.eval value2671 (momentVector H) := by
  have heq : pivotMatrix2671 = (fun u v => node2671 (pivotPermutation2671 u) v) := by apply Matrix.ext; unfold pivotMatrix2671 node2671 pivotPermutation2671; decide +kernel
  have hmoment : injectiveMoment H node2671 = injectiveMoment H pivotMatrix2671 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2671 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2671 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2671 (0 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2671 (0 : Fin 5) = raw5895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2671 raw5895; decide +kernel
    rw [heq]
    exact (canonical5895 hH).trans (sound876 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2671 (1 : Fin 5)) =
      Sparse.eval value709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2671 (1 : Fin 5) = raw6750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2671 raw6750; decide +kernel
    rw [heq]
    exact (canonical6750 hH).trans (sound709 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2671 (2 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2671 (2 : Fin 5) = raw6758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2671 raw6758; decide +kernel
    rw [heq]
    exact (canonical6758 hH).trans (sound1143 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2671 (3 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2671 (3 : Fin 5) = raw6760 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2671 raw6760; decide +kernel
    rw [heq]
    exact (canonical6760 hH).trans (sound872 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2671 (4 : Fin 5)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2671 (4 : Fin 5) = raw6761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2671 raw6761; decide +kernel
    rw [heq]
    exact (canonical6761 hH).trans (sound872 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2671 + (injectiveMoment H (mergeFirst pivotMatrix2671 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2671 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2671 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2671 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2671 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2671, value1143, value709, value872, value876, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2672 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2672 = Sparse.eval value2672 (momentVector H) := by
  have heq : pivotMatrix2672 = (fun u v => node2672 (pivotPermutation2672 u) v) := by apply Matrix.ext; unfold pivotMatrix2672 node2672 pivotPermutation2672; decide +kernel
  have hmoment : injectiveMoment H node2672 = injectiveMoment H pivotMatrix2672 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2672 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2672 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2672 (0 : Fin 5)) =
      Sparse.eval value877 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (0 : Fin 5) = raw5903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw5903; decide +kernel
    rw [heq]
    exact (canonical5903 hH).trans (sound877 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2672 (1 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (1 : Fin 5) = raw6758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6758; decide +kernel
    rw [heq]
    exact (canonical6758 hH).trans (sound1143 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2672 (2 : Fin 5)) =
      Sparse.eval value1144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (2 : Fin 5) = raw6765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6765; decide +kernel
    rw [heq]
    exact (canonical6765 hH).trans (sound1144 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2672 (3 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (3 : Fin 5) = raw6767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6767; decide +kernel
    rw [heq]
    exact (canonical6767 hH).trans (sound743 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2672 (4 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (4 : Fin 5) = raw6768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6768; decide +kernel
    rw [heq]
    exact (canonical6768 hH).trans (sound743 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2672 + (injectiveMoment H (mergeFirst pivotMatrix2672 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2672, value1143, value1144, value743, value877, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2673 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem sound2673 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2673 = Sparse.eval value2673 (momentVector H) := by
  have heq : pivotMatrix2673 = (fun u v => node2673 (pivotPermutation2673 u) v) := by apply Matrix.ext; unfold pivotMatrix2673 node2673 pivotPermutation2673; decide +kernel
  have hmoment : injectiveMoment H node2673 = injectiveMoment H pivotMatrix2673 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2673 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2673 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2673 (0 : Fin 5)) =
      Sparse.eval value880 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2673 (0 : Fin 5) = raw5923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2673 raw5923; decide +kernel
    rw [heq]
    exact (canonical5923 hH).trans (sound880 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2673 (1 : Fin 5)) =
      Sparse.eval value1145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2673 (1 : Fin 5) = raw6777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2673 raw6777; decide +kernel
    rw [heq]
    exact (canonical6777 hH).trans (sound1145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2673 (2 : Fin 5)) =
      Sparse.eval value1145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2673 (2 : Fin 5) = raw6796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2673 raw6796; decide +kernel
    rw [heq]
    exact (canonical6796 hH).trans (sound1145 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2673 (3 : Fin 5)) =
      Sparse.eval value1149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2673 (3 : Fin 5) = raw6798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2673 raw6798; decide +kernel
    rw [heq]
    exact (canonical6798 hH).trans (sound1149 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2673 (4 : Fin 5)) =
      Sparse.eval value1150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2673 (4 : Fin 5) = raw6799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2673 raw6799; decide +kernel
    rw [heq]
    exact (canonical6799 hH).trans (sound1150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2673 + (injectiveMoment H (mergeFirst pivotMatrix2673 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2673 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2673 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2673 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2673 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2673, value1145, value1149, value1150, value880, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2674 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem sound2674 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2674 = Sparse.eval value2674 (momentVector H) := by
  have heq : pivotMatrix2674 = (fun u v => node2674 (pivotPermutation2674 u) v) := by apply Matrix.ext; unfold pivotMatrix2674 node2674 pivotPermutation2674; decide +kernel
  have hmoment : injectiveMoment H node2674 = injectiveMoment H pivotMatrix2674 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2674 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2674 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2674 (0 : Fin 5)) =
      Sparse.eval value882 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2674 (0 : Fin 5) = raw5928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2674 raw5928; decide +kernel
    rw [heq]
    exact (canonical5928 hH).trans (sound882 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2674 (1 : Fin 5)) =
      Sparse.eval value1147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2674 (1 : Fin 5) = raw6778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2674 raw6778; decide +kernel
    rw [heq]
    exact (canonical6778 hH).trans (sound1147 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2674 (2 : Fin 5)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2674 (2 : Fin 5) = raw6805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2674 raw6805; decide +kernel
    rw [heq]
    exact (canonical6805 hH).trans (sound284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2674 (3 : Fin 5)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2674 (3 : Fin 5) = raw6807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2674 raw6807; decide +kernel
    rw [heq]
    exact (canonical6807 hH).trans (sound1151 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2674 (4 : Fin 5)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2674 (4 : Fin 5) = raw6808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2674 raw6808; decide +kernel
    rw [heq]
    exact (canonical6808 hH).trans (sound1152 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2674 + (injectiveMoment H (mergeFirst pivotMatrix2674 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2674 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2674 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2674 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2674 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2674, value1147, value1151, value1152, value284, value882, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2675 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem sound2675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2675 = Sparse.eval value2675 (momentVector H) := by
  have heq : pivotMatrix2675 = (fun u v => node2675 (pivotPermutation2675 u) v) := by apply Matrix.ext; unfold pivotMatrix2675 node2675 pivotPermutation2675; decide +kernel
  have hmoment : injectiveMoment H node2675 = injectiveMoment H pivotMatrix2675 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2675 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2675 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2675 (0 : Fin 5)) =
      Sparse.eval value884 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2675 (0 : Fin 5) = raw5959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2675 raw5959; decide +kernel
    rw [heq]
    exact (canonical5959 hH).trans (sound884 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2675 (1 : Fin 5)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2675 (1 : Fin 5) = raw6829 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2675 raw6829; decide +kernel
    rw [heq]
    exact (canonical6829 hH).trans (sound287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2675 (2 : Fin 5)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2675 (2 : Fin 5) = raw6838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2675 raw6838; decide +kernel
    rw [heq]
    exact (canonical6838 hH).trans (sound287 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2675 (3 : Fin 5)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2675 (3 : Fin 5) = raw6842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2675 raw6842; decide +kernel
    rw [heq]
    exact (canonical6842 hH).trans (sound287 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2675 (4 : Fin 5)) =
      Sparse.eval value1153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2675 (4 : Fin 5) = raw6843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2675 raw6843; decide +kernel
    rw [heq]
    exact (canonical6843 hH).trans (sound1153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2675 + (injectiveMoment H (mergeFirst pivotMatrix2675 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2675 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2675 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2675 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2675 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2675, value1153, value287, value884, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2676 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2676 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2676 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2676 = Sparse.eval value2676 (momentVector H) := by
  have heq : pivotMatrix2676 = (fun u v => node2676 (pivotPermutation2676 u) v) := by apply Matrix.ext; unfold pivotMatrix2676 node2676 pivotPermutation2676; decide +kernel
  have hmoment : injectiveMoment H node2676 = injectiveMoment H pivotMatrix2676 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2676 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2676 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2676 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2676 (0 : Fin 4) = raw7562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2676 raw7562; decide +kernel
    rw [heq]
    exact (canonical7562 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2676 (1 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2676 (1 : Fin 4) = raw6926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2676 raw6926; decide +kernel
    rw [heq]
    exact (canonical6926 hH).trans (sound1054 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2676 (2 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2676 (2 : Fin 4) = raw6919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2676 raw6919; decide +kernel
    rw [heq]
    exact (canonical6919 hH).trans (sound807 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2676 (3 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2676 (3 : Fin 4) = raw6918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2676 raw6918; decide +kernel
    rw [heq]
    exact (canonical6918 hH).trans (sound805 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2676 + (injectiveMoment H (mergeFirst pivotMatrix2676 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2676 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2676 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2676 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2676, value1054, value805, value807, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2677 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2677 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2677 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2677 = Sparse.eval value2677 (momentVector H) := by
  have heq : pivotMatrix2677 = (fun u v => node2677 (pivotPermutation2677 u) v) := by apply Matrix.ext; unfold pivotMatrix2677 node2677 pivotPermutation2677; decide +kernel
  have hmoment : injectiveMoment H node2677 = injectiveMoment H pivotMatrix2677 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2677 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2677 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2677 (0 : Fin 4)) =
      Sparse.eval value919 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2677 (0 : Fin 4) = raw7612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2677 raw7612; decide +kernel
    rw [heq]
    exact (canonical7612 hH).trans (sound919 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2677 (1 : Fin 4)) =
      Sparse.eval value978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2677 (1 : Fin 4) = raw6964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2677 raw6964; decide +kernel
    rw [heq]
    exact (canonical6964 hH).trans (sound978 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2677 (2 : Fin 4)) =
      Sparse.eval value782 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2677 (2 : Fin 4) = raw6963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2677 raw6963; decide +kernel
    rw [heq]
    exact (canonical6963 hH).trans (sound782 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2677 (3 : Fin 4)) =
      Sparse.eval value779 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2677 (3 : Fin 4) = raw6962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2677 raw6962; decide +kernel
    rw [heq]
    exact (canonical6962 hH).trans (sound779 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2677 + (injectiveMoment H (mergeFirst pivotMatrix2677 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2677 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2677 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2677 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2677, value779, value782, value919, value978, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2678 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2678 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem sound2678 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2678 = Sparse.eval value2678 (momentVector H) := by
  have heq : pivotMatrix2678 = (fun u v => node2678 (pivotPermutation2678 u) v) := by apply Matrix.ext; unfold pivotMatrix2678 node2678 pivotPermutation2678; decide +kernel
  have hmoment : injectiveMoment H node2678 = injectiveMoment H pivotMatrix2678 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2678 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2678 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2678 (0 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2678 (0 : Fin 4) = raw8275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2678 raw8275; decide +kernel
    rw [heq]
    exact (canonical8275 hH).trans (sound1341 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2678 (1 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2678 (1 : Fin 4) = raw7012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2678 raw7012; decide +kernel
    rw [heq]
    exact (canonical7012 hH).trans (sound1176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2678 (2 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2678 (2 : Fin 4) = raw6980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2678 raw6980; decide +kernel
    rw [heq]
    exact (canonical6980 hH).trans (sound1341 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2678 (3 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2678 (3 : Fin 4) = raw6976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2678 raw6976; decide +kernel
    rw [heq]
    exact (canonical6976 hH).trans (sound453 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2678 + (injectiveMoment H (mergeFirst pivotMatrix2678 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2678 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2678 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2678 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2678, value1176, value1341, value453, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2679 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2679 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem sound2679 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2679 = Sparse.eval value2679 (momentVector H) := by
  have heq : pivotMatrix2679 = (fun u v => node2679 (pivotPermutation2679 u) v) := by apply Matrix.ext; unfold pivotMatrix2679 node2679 pivotPermutation2679; decide +kernel
  have hmoment : injectiveMoment H node2679 = injectiveMoment H pivotMatrix2679 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2679 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2679 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2679 (0 : Fin 4)) =
      Sparse.eval value1354 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2679 (0 : Fin 4) = raw8276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2679 raw8276; decide +kernel
    rw [heq]
    exact (canonical8276 hH).trans (sound1354 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2679 (1 : Fin 4)) =
      Sparse.eval value1167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2679 (1 : Fin 4) = raw7013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2679 raw7013; decide +kernel
    rw [heq]
    exact (canonical7013 hH).trans (sound1167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2679 (2 : Fin 4)) =
      Sparse.eval value1340 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2679 (2 : Fin 4) = raw6981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2679 raw6981; decide +kernel
    rw [heq]
    exact (canonical6981 hH).trans (sound1340 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2679 (3 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2679 (3 : Fin 4) = raw6978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2679 raw6978; decide +kernel
    rw [heq]
    exact (canonical6978 hH).trans (sound688 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2679 + (injectiveMoment H (mergeFirst pivotMatrix2679 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2679 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2679 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2679 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2679, value1167, value1340, value1354, value688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2680 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2680 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem sound2680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2680 = Sparse.eval value2680 (momentVector H) := by
  have heq : pivotMatrix2680 = (fun u v => node2680 (pivotPermutation2680 u) v) := by apply Matrix.ext; unfold pivotMatrix2680 node2680 pivotPermutation2680; decide +kernel
  have hmoment : injectiveMoment H node2680 = injectiveMoment H pivotMatrix2680 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2680 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2680 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2680 (0 : Fin 4)) =
      Sparse.eval value1298 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2680 (0 : Fin 4) = raw8277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2680 raw8277; decide +kernel
    rw [heq]
    exact (canonical8277 hH).trans (sound1298 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2680 (1 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2680 (1 : Fin 4) = raw7019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2680 raw7019; decide +kernel
    rw [heq]
    exact (canonical7019 hH).trans (sound1178 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2680 (2 : Fin 4)) =
      Sparse.eval value1095 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2680 (2 : Fin 4) = raw6984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2680 raw6984; decide +kernel
    rw [heq]
    exact (canonical6984 hH).trans (sound1095 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2680 (3 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2680 (3 : Fin 4) = raw6983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2680 raw6983; decide +kernel
    rw [heq]
    exact (canonical6983 hH).trans (sound584 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2680 + (injectiveMoment H (mergeFirst pivotMatrix2680 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2680 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2680 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2680 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2680, value1095, value1178, value1298, value584, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2681 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2681 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2681 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2681 = Sparse.eval value2681 (momentVector H) := by
  have heq : pivotMatrix2681 = (fun u v => node2681 (pivotPermutation2681 u) v) := by apply Matrix.ext; unfold pivotMatrix2681 node2681 pivotPermutation2681; decide +kernel
  have hmoment : injectiveMoment H node2681 = injectiveMoment H pivotMatrix2681 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2681 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2681 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2681 (0 : Fin 4)) =
      Sparse.eval value806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2681 (0 : Fin 4) = raw7065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2681 raw7065; decide +kernel
    rw [heq]
    exact (canonical7065 hH).trans (sound806 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2681 (1 : Fin 4)) =
      Sparse.eval value781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2681 (1 : Fin 4) = raw6990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2681 raw6990; decide +kernel
    rw [heq]
    exact (canonical6990 hH).trans (sound781 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2681 (2 : Fin 4)) =
      Sparse.eval value1165 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2681 (2 : Fin 4) = raw6987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2681 raw6987; decide +kernel
    rw [heq]
    exact (canonical6987 hH).trans (sound1165 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2681 (3 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2681 (3 : Fin 4) = raw6986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2681 raw6986; decide +kernel
    rw [heq]
    exact (canonical6986 hH).trans (sound1164 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2681 + (injectiveMoment H (mergeFirst pivotMatrix2681 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2681 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2681 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2681 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2681, value1164, value1165, value781, value806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2682 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2682 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound2682 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2682 = Sparse.eval value2682 (momentVector H) := by
  have heq : pivotMatrix2682 = (fun u v => node2682 (pivotPermutation2682 u) v) := by apply Matrix.ext; unfold pivotMatrix2682 node2682 pivotPermutation2682; decide +kernel
  have hmoment : injectiveMoment H node2682 = injectiveMoment H pivotMatrix2682 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2682 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2682 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2682 (0 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (0 : Fin 4) = raw7774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw7774; decide +kernel
    rw [heq]
    exact (canonical7774 hH).trans (sound977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2682 (1 : Fin 4)) =
      Sparse.eval value919 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (1 : Fin 4) = raw7002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw7002; decide +kernel
    rw [heq]
    exact (canonical7002 hH).trans (sound919 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2682 (2 : Fin 4)) =
      Sparse.eval value781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (2 : Fin 4) = raw6990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw6990; decide +kernel
    rw [heq]
    exact (canonical6990 hH).trans (sound781 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2682 (3 : Fin 4)) =
      Sparse.eval value780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2682 (3 : Fin 4) = raw6989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2682 raw6989; decide +kernel
    rw [heq]
    exact (canonical6989 hH).trans (sound780 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2682 + (injectiveMoment H (mergeFirst pivotMatrix2682 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2682 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2682 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2682 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2682, value780, value781, value919, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2683 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2683 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem sound2683 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2683 = Sparse.eval value2683 (momentVector H) := by
  have heq : pivotMatrix2683 = (fun u v => node2683 (pivotPermutation2683 u) v) := by apply Matrix.ext; unfold pivotMatrix2683 node2683 pivotPermutation2683; decide +kernel
  have hmoment : injectiveMoment H node2683 = injectiveMoment H pivotMatrix2683 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2683 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2683 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2683 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (0 : Fin 4) = raw6036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6036; decide +kernel
    rw [heq]
    exact (canonical6036 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2683 (1 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (1 : Fin 4) = raw6986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6986; decide +kernel
    rw [heq]
    exact (canonical6986 hH).trans (sound1164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2683 (2 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (2 : Fin 4) = raw6994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6994; decide +kernel
    rw [heq]
    exact (canonical6994 hH).trans (sound1168 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2683 (3 : Fin 4)) =
      Sparse.eval value1169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (3 : Fin 4) = raw6995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6995; decide +kernel
    rw [heq]
    exact (canonical6995 hH).trans (sound1169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2683 + (injectiveMoment H (mergeFirst pivotMatrix2683 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2683 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2683 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2683 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2683, value1164, value1168, value1169, value771, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2684 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2684 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound2684 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2684 = Sparse.eval value2684 (momentVector H) := by
  have heq : pivotMatrix2684 = (fun u v => node2684 (pivotPermutation2684 u) v) := by apply Matrix.ext; unfold pivotMatrix2684 node2684 pivotPermutation2684; decide +kernel
  have hmoment : injectiveMoment H node2684 = injectiveMoment H pivotMatrix2684 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2684 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2684 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2684 (0 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2684 (0 : Fin 4) = raw6044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2684 raw6044; decide +kernel
    rw [heq]
    exact (canonical6044 hH).trans (sound774 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2684 (1 : Fin 4)) =
      Sparse.eval value781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2684 (1 : Fin 4) = raw6990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2684 raw6990; decide +kernel
    rw [heq]
    exact (canonical6990 hH).trans (sound781 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2684 (2 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2684 (2 : Fin 4) = raw6998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2684 raw6998; decide +kernel
    rw [heq]
    exact (canonical6998 hH).trans (sound1171 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2684 (3 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2684 (3 : Fin 4) = raw6999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2684 raw6999; decide +kernel
    rw [heq]
    exact (canonical6999 hH).trans (sound1173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2684 + (injectiveMoment H (mergeFirst pivotMatrix2684 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2684 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2684 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2684 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2684, value1171, value1173, value774, value781, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2685 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2685 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2685 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2685 = Sparse.eval value2685 (momentVector H) := by
  have heq : pivotMatrix2685 = (fun u v => node2685 (pivotPermutation2685 u) v) := by apply Matrix.ext; unfold pivotMatrix2685 node2685 pivotPermutation2685; decide +kernel
  have hmoment : injectiveMoment H node2685 = injectiveMoment H pivotMatrix2685 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2685 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2685 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2685 (0 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2685 (0 : Fin 4) = raw6077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2685 raw6077; decide +kernel
    rw [heq]
    exact (canonical6077 hH).trans (sound910 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2685 (1 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2685 (1 : Fin 4) = raw6998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2685 raw6998; decide +kernel
    rw [heq]
    exact (canonical6998 hH).trans (sound1171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2685 (2 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2685 (2 : Fin 4) = raw7008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2685 raw7008; decide +kernel
    rw [heq]
    exact (canonical7008 hH).trans (sound254 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2685 (3 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2685 (3 : Fin 4) = raw7012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2685 raw7012; decide +kernel
    rw [heq]
    exact (canonical7012 hH).trans (sound1176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2685 + (injectiveMoment H (mergeFirst pivotMatrix2685 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2685 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2685 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2685 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2685, value1171, value1176, value254, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2686 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2686 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem sound2686 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2686 = Sparse.eval value2686 (momentVector H) := by
  have heq : pivotMatrix2686 = (fun u v => node2686 (pivotPermutation2686 u) v) := by apply Matrix.ext; unfold pivotMatrix2686 node2686 pivotPermutation2686; decide +kernel
  have hmoment : injectiveMoment H node2686 = injectiveMoment H pivotMatrix2686 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2686 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2686 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2686 (0 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2686 (0 : Fin 4) = raw6080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2686 raw6080; decide +kernel
    rw [heq]
    exact (canonical6080 hH).trans (sound769 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2686 (1 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2686 (1 : Fin 4) = raw6999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2686 raw6999; decide +kernel
    rw [heq]
    exact (canonical6999 hH).trans (sound1173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2686 (2 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2686 (2 : Fin 4) = raw7012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2686 raw7012; decide +kernel
    rw [heq]
    exact (canonical7012 hH).trans (sound1176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2686 (3 : Fin 4)) =
      Sparse.eval value768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2686 (3 : Fin 4) = raw7014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2686 raw7014; decide +kernel
    rw [heq]
    exact (canonical7014 hH).trans (sound768 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2686 + (injectiveMoment H (mergeFirst pivotMatrix2686 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2686 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2686 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2686 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2686, value1173, value1176, value768, value769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2687 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2687 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem sound2687 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2687 = Sparse.eval value2687 (momentVector H) := by
  have heq : pivotMatrix2687 = (fun u v => node2687 (pivotPermutation2687 u) v) := by apply Matrix.ext; unfold pivotMatrix2687 node2687 pivotPermutation2687; decide +kernel
  have hmoment : injectiveMoment H node2687 = injectiveMoment H pivotMatrix2687 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2687 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2687 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2687 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (0 : Fin 4) = raw6090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw6090; decide +kernel
    rw [heq]
    exact (canonical6090 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2687 (1 : Fin 4)) =
      Sparse.eval value1175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (1 : Fin 4) = raw7003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw7003; decide +kernel
    rw [heq]
    exact (canonical7003 hH).trans (sound1175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2687 (2 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (2 : Fin 4) = raw7019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw7019; decide +kernel
    rw [heq]
    exact (canonical7019 hH).trans (sound1178 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2687 (3 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (3 : Fin 4) = raw7020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw7020; decide +kernel
    rw [heq]
    exact (canonical7020 hH).trans (sound1180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2687 + (injectiveMoment H (mergeFirst pivotMatrix2687 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2687 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2687 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2687 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2687, value1175, value1178, value1180, value775, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
