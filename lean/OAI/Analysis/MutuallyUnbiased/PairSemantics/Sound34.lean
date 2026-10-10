import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical134
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical135
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical136
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical141
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical149
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical150
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2176 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2176 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound2176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2176 = Sparse.eval value2176 (momentVector H) := by
  have heq : pivotMatrix2176 = (fun u v => node2176 (pivotPermutation2176 u) v) := by apply Matrix.ext; unfold pivotMatrix2176 node2176 pivotPermutation2176; decide +kernel
  have hmoment : injectiveMoment H node2176 = injectiveMoment H pivotMatrix2176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2176 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2176 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2176 (0 : Fin 4)) =
      Sparse.eval value1073 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2176 (0 : Fin 4) = raw5259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2176 raw5259; decide +kernel
    rw [heq]
    exact (canonical5259 hH).trans (sound1073 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2176 (1 : Fin 4)) =
      Sparse.eval value1072 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2176 (1 : Fin 4) = raw4411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2176 raw4411; decide +kernel
    rw [heq]
    exact (canonical4411 hH).trans (sound1072 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2176 (2 : Fin 4)) =
      Sparse.eval value1046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2176 (2 : Fin 4) = raw4330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2176 raw4330; decide +kernel
    rw [heq]
    exact (canonical4330 hH).trans (sound1046 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2176 (3 : Fin 4)) =
      Sparse.eval value674 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2176 (3 : Fin 4) = raw4328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2176 raw4328; decide +kernel
    rw [heq]
    exact (canonical4328 hH).trans (sound674 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2176 + (injectiveMoment H (mergeFirst pivotMatrix2176 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2176 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2176 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2176 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2176, value1046, value1072, value1073, value674, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2177 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2177 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound2177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2177 = Sparse.eval value2177 (momentVector H) := by
  have heq : pivotMatrix2177 = (fun u v => node2177 (pivotPermutation2177 u) v) := by apply Matrix.ext; unfold pivotMatrix2177 node2177 pivotPermutation2177; decide +kernel
  have hmoment : injectiveMoment H node2177 = injectiveMoment H pivotMatrix2177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2177 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2177 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2177 (0 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2177 (0 : Fin 4) = raw5260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2177 raw5260; decide +kernel
    rw [heq]
    exact (canonical5260 hH).trans (sound1052 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2177 (1 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2177 (1 : Fin 4) = raw4412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2177 raw4412; decide +kernel
    rw [heq]
    exact (canonical4412 hH).trans (sound1062 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2177 (2 : Fin 4)) =
      Sparse.eval value1046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2177 (2 : Fin 4) = raw4331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2177 raw4331; decide +kernel
    rw [heq]
    exact (canonical4331 hH).trans (sound1046 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2177 (3 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2177 (3 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2177 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2177 + (injectiveMoment H (mergeFirst pivotMatrix2177 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2177 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2177 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2177 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2177, value1046, value1052, value1062, value1074, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2178 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2178 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound2178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2178 = Sparse.eval value2178 (momentVector H) := by
  have heq : pivotMatrix2178 = (fun u v => node2178 (pivotPermutation2178 u) v) := by apply Matrix.ext; unfold pivotMatrix2178 node2178 pivotPermutation2178; decide +kernel
  have hmoment : injectiveMoment H node2178 = injectiveMoment H pivotMatrix2178 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2178 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2178 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2178 (0 : Fin 4)) =
      Sparse.eval value913 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2178 (0 : Fin 4) = raw4260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2178 raw4260; decide +kernel
    rw [heq]
    exact (canonical4260 hH).trans (sound913 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2178 (1 : Fin 4)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2178 (1 : Fin 4) = raw4347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2178 raw4347; decide +kernel
    rw [heq]
    exact (canonical4347 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2178 (2 : Fin 4)) =
      Sparse.eval value1219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2178 (2 : Fin 4) = raw4369 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2178 raw4369; decide +kernel
    rw [heq]
    exact (canonical4369 hH).trans (sound1219 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2178 (3 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2178 (3 : Fin 4) = raw4373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2178 raw4373; decide +kernel
    rw [heq]
    exact (canonical4373 hH).trans (sound973 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2178 + (injectiveMoment H (mergeFirst pivotMatrix2178 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2178 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2178 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2178 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2178, value1219, value274, value913, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2179 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2179 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

theorem sound2179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2179 = Sparse.eval value2179 (momentVector H) := by
  have heq : pivotMatrix2179 = (fun u v => node2179 (pivotPermutation2179 u) v) := by apply Matrix.ext; unfold pivotMatrix2179 node2179 pivotPermutation2179; decide +kernel
  have hmoment : injectiveMoment H node2179 = injectiveMoment H pivotMatrix2179 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2179 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2179 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2179 (0 : Fin 4)) =
      Sparse.eval value932 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2179 (0 : Fin 4) = raw4265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2179 raw4265; decide +kernel
    rw [heq]
    exact (canonical4265 hH).trans (sound932 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2179 (1 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2179 (1 : Fin 4) = raw4350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2179 raw4350; decide +kernel
    rw [heq]
    exact (canonical4350 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2179 (2 : Fin 4)) =
      Sparse.eval value1239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2179 (2 : Fin 4) = raw4381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2179 raw4381; decide +kernel
    rw [heq]
    exact (canonical4381 hH).trans (sound1239 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2179 (3 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2179 (3 : Fin 4) = raw4382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2179 raw4382; decide +kernel
    rw [heq]
    exact (canonical4382 hH).trans (sound815 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2179 + (injectiveMoment H (mergeFirst pivotMatrix2179 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2179 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2179 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2179 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2179, value1239, value223, value815, value932, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2180 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2180 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

theorem sound2180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2180 = Sparse.eval value2180 (momentVector H) := by
  have heq : pivotMatrix2180 = (fun u v => node2180 (pivotPermutation2180 u) v) := by apply Matrix.ext; unfold pivotMatrix2180 node2180 pivotPermutation2180; decide +kernel
  have hmoment : injectiveMoment H node2180 = injectiveMoment H pivotMatrix2180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2180 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2180 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2180 (0 : Fin 4)) =
      Sparse.eval value784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2180 (0 : Fin 4) = raw4266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2180 raw4266; decide +kernel
    rw [heq]
    exact (canonical4266 hH).trans (sound784 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2180 (1 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2180 (1 : Fin 4) = raw4351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2180 raw4351; decide +kernel
    rw [heq]
    exact (canonical4351 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2180 (2 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2180 (2 : Fin 4) = raw4382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2180 raw4382; decide +kernel
    rw [heq]
    exact (canonical4382 hH).trans (sound815 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2180 (3 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2180 (3 : Fin 4) = raw4383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2180 raw4383; decide +kernel
    rw [heq]
    exact (canonical4383 hH).trans (sound983 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2180 + (injectiveMoment H (mergeFirst pivotMatrix2180 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2180 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2180 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2180 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2180, value184, value784, value815, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2181 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2181 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

theorem sound2181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2181 = Sparse.eval value2181 (momentVector H) := by
  have heq : pivotMatrix2181 = (fun u v => node2181 (pivotPermutation2181 u) v) := by apply Matrix.ext; unfold pivotMatrix2181 node2181 pivotPermutation2181; decide +kernel
  have hmoment : injectiveMoment H node2181 = injectiveMoment H pivotMatrix2181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2181 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2181 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2181 (0 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2181 (0 : Fin 4) = raw4271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2181 raw4271; decide +kernel
    rw [heq]
    exact (canonical4271 hH).trans (sound400 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2181 (1 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2181 (1 : Fin 4) = raw4382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2181 raw4382; decide +kernel
    rw [heq]
    exact (canonical4382 hH).trans (sound815 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2181 (2 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2181 (2 : Fin 4) = raw4398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2181 raw4398; decide +kernel
    rw [heq]
    exact (canonical4398 hH).trans (sound408 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2181 (3 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2181 (3 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2181 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2181 + (injectiveMoment H (mergeFirst pivotMatrix2181 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2181 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2181 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2181 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2181, value400, value408, value484, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2182 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2182 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound2182 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2182 = Sparse.eval value2182 (momentVector H) := by
  have heq : pivotMatrix2182 = (fun u v => node2182 (pivotPermutation2182 u) v) := by apply Matrix.ext; unfold pivotMatrix2182 node2182 pivotPermutation2182; decide +kernel
  have hmoment : injectiveMoment H node2182 = injectiveMoment H pivotMatrix2182 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2182 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2182 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2182 (0 : Fin 4)) =
      Sparse.eval value1022 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2182 (0 : Fin 4) = raw4288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2182 raw4288; decide +kernel
    rw [heq]
    exact (canonical4288 hH).trans (sound1022 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2182 (1 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2182 (1 : Fin 4) = raw4432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2182 raw4432; decide +kernel
    rw [heq]
    exact (canonical4432 hH).trans (sound1028 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2182 (2 : Fin 4)) =
      Sparse.eval value1019 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2182 (2 : Fin 4) = raw4434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2182 raw4434; decide +kernel
    rw [heq]
    exact (canonical4434 hH).trans (sound1019 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2182 (3 : Fin 4)) =
      Sparse.eval value1019 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2182 (3 : Fin 4) = raw4435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2182 raw4435; decide +kernel
    rw [heq]
    exact (canonical4435 hH).trans (sound1019 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2182 + (injectiveMoment H (mergeFirst pivotMatrix2182 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2182 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2182 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2182 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2182, value1019, value1022, value1028, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2183 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2183 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem sound2183 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2183 = Sparse.eval value2183 (momentVector H) := by
  have heq : pivotMatrix2183 = (fun u v => node2183 (pivotPermutation2183 u) v) := by apply Matrix.ext; unfold pivotMatrix2183 node2183 pivotPermutation2183; decide +kernel
  have hmoment : injectiveMoment H node2183 = injectiveMoment H pivotMatrix2183 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2183 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2183 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2183 (0 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2183 (0 : Fin 4) = raw4564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2183 raw4564; decide +kernel
    rw [heq]
    exact (canonical4564 hH).trans (sound1263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2183 (1 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2183 (1 : Fin 4) = raw4391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2183 raw4391; decide +kernel
    rw [heq]
    exact (canonical4391 hH).trans (sound1315 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2183 (2 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2183 (2 : Fin 4) = raw4373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2183 raw4373; decide +kernel
    rw [heq]
    exact (canonical4373 hH).trans (sound973 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2183 (3 : Fin 4)) =
      Sparse.eval value1219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2183 (3 : Fin 4) = raw4369 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2183 raw4369; decide +kernel
    rw [heq]
    exact (canonical4369 hH).trans (sound1219 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2183 + (injectiveMoment H (mergeFirst pivotMatrix2183 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2183 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2183 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2183 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2183, value1219, value1263, value1315, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2184 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2184 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

theorem sound2184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2184 = Sparse.eval value2184 (momentVector H) := by
  have heq : pivotMatrix2184 = (fun u v => node2184 (pivotPermutation2184 u) v) := by apply Matrix.ext; unfold pivotMatrix2184 node2184 pivotPermutation2184; decide +kernel
  have hmoment : injectiveMoment H node2184 = injectiveMoment H pivotMatrix2184 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2184 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2184 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2184 (0 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2184 (0 : Fin 4) = raw4569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2184 raw4569; decide +kernel
    rw [heq]
    exact (canonical4569 hH).trans (sound842 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2184 (1 : Fin 4)) =
      Sparse.eval value407 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2184 (1 : Fin 4) = raw4397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2184 raw4397; decide +kernel
    rw [heq]
    exact (canonical4397 hH).trans (sound407 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2184 (2 : Fin 4)) =
      Sparse.eval value725 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2184 (2 : Fin 4) = raw4380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2184 raw4380; decide +kernel
    rw [heq]
    exact (canonical4380 hH).trans (sound725 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2184 (3 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2184 (3 : Fin 4) = raw4377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2184 raw4377; decide +kernel
    rw [heq]
    exact (canonical4377 hH).trans (sound804 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2184 + (injectiveMoment H (mergeFirst pivotMatrix2184 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2184 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2184 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2184 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2184, value407, value725, value804, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2185 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2185 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem sound2185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2185 = Sparse.eval value2185 (momentVector H) := by
  have heq : pivotMatrix2185 = (fun u v => node2185 (pivotPermutation2185 u) v) := by apply Matrix.ext; unfold pivotMatrix2185 node2185 pivotPermutation2185; decide +kernel
  have hmoment : injectiveMoment H node2185 = injectiveMoment H pivotMatrix2185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2185 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2185 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2185 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2185 (0 : Fin 4) = raw4571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2185 raw4571; decide +kernel
    rw [heq]
    exact (canonical4571 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2185 (1 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2185 (1 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2185 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2185 (2 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2185 (2 : Fin 4) = raw4383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2185 raw4383; decide +kernel
    rw [heq]
    exact (canonical4383 hH).trans (sound983 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2185 (3 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2185 (3 : Fin 4) = raw4382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2185 raw4382; decide +kernel
    rw [heq]
    exact (canonical4382 hH).trans (sound815 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2185 + (injectiveMoment H (mergeFirst pivotMatrix2185 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2185 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2185 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2185 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2185, value1078, value484, value815, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2186 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2186 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem sound2186 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2186 = Sparse.eval value2186 (momentVector H) := by
  have heq : pivotMatrix2186 = (fun u v => node2186 (pivotPermutation2186 u) v) := by apply Matrix.ext; unfold pivotMatrix2186 node2186 pivotPermutation2186; decide +kernel
  have hmoment : injectiveMoment H node2186 = injectiveMoment H pivotMatrix2186 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2186 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2186 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2186 (0 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2186 (0 : Fin 4) = raw4580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2186 raw4580; decide +kernel
    rw [heq]
    exact (canonical4580 hH).trans (sound1314 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2186 (1 : Fin 4)) =
      Sparse.eval value1321 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2186 (1 : Fin 4) = raw4406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2186 raw4406; decide +kernel
    rw [heq]
    exact (canonical4406 hH).trans (sound1321 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2186 (2 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2186 (2 : Fin 4) = raw4394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2186 raw4394; decide +kernel
    rw [heq]
    exact (canonical4394 hH).trans (sound808 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2186 (3 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2186 (3 : Fin 4) = raw4391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2186 raw4391; decide +kernel
    rw [heq]
    exact (canonical4391 hH).trans (sound1315 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2186 + (injectiveMoment H (mergeFirst pivotMatrix2186 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2186 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2186 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2186 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2186, value1314, value1315, value1321, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2187 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2187 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

theorem sound2187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2187 = Sparse.eval value2187 (momentVector H) := by
  have heq : pivotMatrix2187 = (fun u v => node2187 (pivotPermutation2187 u) v) := by apply Matrix.ext; unfold pivotMatrix2187 node2187 pivotPermutation2187; decide +kernel
  have hmoment : injectiveMoment H node2187 = injectiveMoment H pivotMatrix2187 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2187 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2187 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2187 (0 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2187 (0 : Fin 4) = raw4584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2187 raw4584; decide +kernel
    rw [heq]
    exact (canonical4584 hH).trans (sound844 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2187 (1 : Fin 4)) =
      Sparse.eval value727 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2187 (1 : Fin 4) = raw4409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2187 raw4409; decide +kernel
    rw [heq]
    exact (canonical4409 hH).trans (sound727 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2187 (2 : Fin 4)) =
      Sparse.eval value407 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2187 (2 : Fin 4) = raw4397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2187 raw4397; decide +kernel
    rw [heq]
    exact (canonical4397 hH).trans (sound407 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2187 (3 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2187 (3 : Fin 4) = raw4394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2187 raw4394; decide +kernel
    rw [heq]
    exact (canonical4394 hH).trans (sound808 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2187 + (injectiveMoment H (mergeFirst pivotMatrix2187 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2187 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2187 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2187 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2187, value407, value727, value808, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2188 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2188 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

theorem sound2188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2188 = Sparse.eval value2188 (momentVector H) := by
  have heq : pivotMatrix2188 = (fun u v => node2188 (pivotPermutation2188 u) v) := by apply Matrix.ext; unfold pivotMatrix2188 node2188 pivotPermutation2188; decide +kernel
  have hmoment : injectiveMoment H node2188 = injectiveMoment H pivotMatrix2188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2188 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2188 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2188 (0 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2188 (0 : Fin 4) = raw4586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2188 raw4586; decide +kernel
    rw [heq]
    exact (canonical4586 hH).trans (sound510 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2188 (1 : Fin 4)) =
      Sparse.eval value675 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2188 (1 : Fin 4) = raw4410 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2188 raw4410; decide +kernel
    rw [heq]
    exact (canonical4410 hH).trans (sound675 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2188 (2 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2188 (2 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2188 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2188 (3 : Fin 4)) =
      Sparse.eval value408 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2188 (3 : Fin 4) = raw4398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2188 raw4398; decide +kernel
    rw [heq]
    exact (canonical4398 hH).trans (sound408 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2188 + (injectiveMoment H (mergeFirst pivotMatrix2188 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2188 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2188 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2188 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2188, value408, value484, value510, value675, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2189 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2189 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem sound2189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2189 = Sparse.eval value2189 (momentVector H) := by
  have heq : pivotMatrix2189 = (fun u v => node2189 (pivotPermutation2189 u) v) := by apply Matrix.ext; unfold pivotMatrix2189 node2189 pivotPermutation2189; decide +kernel
  have hmoment : injectiveMoment H node2189 = injectiveMoment H pivotMatrix2189 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2189 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2189 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2189 (0 : Fin 4)) =
      Sparse.eval value1244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2189 (0 : Fin 4) = raw4616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2189 raw4616; decide +kernel
    rw [heq]
    exact (canonical4616 hH).trans (sound1244 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2189 (1 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2189 (1 : Fin 4) = raw4421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2189 raw4421; decide +kernel
    rw [heq]
    exact (canonical4421 hH).trans (sound973 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2189 (2 : Fin 4)) =
      Sparse.eval value1210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2189 (2 : Fin 4) = raw4417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2189 raw4417; decide +kernel
    rw [heq]
    exact (canonical4417 hH).trans (sound1210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2189 (3 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2189 (3 : Fin 4) = raw4416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2189 raw4416; decide +kernel
    rw [heq]
    exact (canonical4416 hH).trans (sound1310 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2189 + (injectiveMoment H (mergeFirst pivotMatrix2189 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2189 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2189 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2189 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2189, value1210, value1244, value1310, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2190 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2190 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound2190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2190 = Sparse.eval value2190 (momentVector H) := by
  have heq : pivotMatrix2190 = (fun u v => node2190 (pivotPermutation2190 u) v) := by apply Matrix.ext; unfold pivotMatrix2190 node2190 pivotPermutation2190; decide +kernel
  have hmoment : injectiveMoment H node2190 = injectiveMoment H pivotMatrix2190 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2190 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2190 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2190 (0 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2190 (0 : Fin 4) = raw4618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2190 raw4618; decide +kernel
    rw [heq]
    exact (canonical4618 hH).trans (sound1263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2190 (1 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2190 (1 : Fin 4) = raw4424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2190 raw4424; decide +kernel
    rw [heq]
    exact (canonical4424 hH).trans (sound1222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2190 (2 : Fin 4)) =
      Sparse.eval value1361 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2190 (2 : Fin 4) = raw4419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2190 raw4419; decide +kernel
    rw [heq]
    exact (canonical4419 hH).trans (sound1361 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2190 (3 : Fin 4)) =
      Sparse.eval value1224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2190 (3 : Fin 4) = raw4418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2190 raw4418; decide +kernel
    rw [heq]
    exact (canonical4418 hH).trans (sound1224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2190 + (injectiveMoment H (mergeFirst pivotMatrix2190 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2190 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2190 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2190 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2190, value1222, value1224, value1263, value1361, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2191 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2191 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem sound2191 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2191 = Sparse.eval value2191 (momentVector H) := by
  have heq : pivotMatrix2191 = (fun u v => node2191 (pivotPermutation2191 u) v) := by apply Matrix.ext; unfold pivotMatrix2191 node2191 pivotPermutation2191; decide +kernel
  have hmoment : injectiveMoment H node2191 = injectiveMoment H pivotMatrix2191 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2191 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2191 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2191 (0 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2191 (0 : Fin 4) = raw4619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2191 raw4619; decide +kernel
    rw [heq]
    exact (canonical4619 hH).trans (sound1360 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2191 (1 : Fin 4)) =
      Sparse.eval value987 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2191 (1 : Fin 4) = raw4425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2191 raw4425; decide +kernel
    rw [heq]
    exact (canonical4425 hH).trans (sound987 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2191 (2 : Fin 4)) =
      Sparse.eval value1361 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2191 (2 : Fin 4) = raw4420 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2191 raw4420; decide +kernel
    rw [heq]
    exact (canonical4420 hH).trans (sound1361 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2191 (3 : Fin 4)) =
      Sparse.eval value1361 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2191 (3 : Fin 4) = raw4419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2191 raw4419; decide +kernel
    rw [heq]
    exact (canonical4419 hH).trans (sound1361 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2191 + (injectiveMoment H (mergeFirst pivotMatrix2191 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2191 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2191 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2191 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2191, value1360, value1361, value987, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2192 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2192 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem sound2192 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2192 = Sparse.eval value2192 (momentVector H) := by
  have heq : pivotMatrix2192 = (fun u v => node2192 (pivotPermutation2192 u) v) := by apply Matrix.ext; unfold pivotMatrix2192 node2192 pivotPermutation2192; decide +kernel
  have hmoment : injectiveMoment H node2192 = injectiveMoment H pivotMatrix2192 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2192 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2192 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2192 (0 : Fin 4)) =
      Sparse.eval value1247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2192 (0 : Fin 4) = raw4620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2192 raw4620; decide +kernel
    rw [heq]
    exact (canonical4620 hH).trans (sound1247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2192 (1 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2192 (1 : Fin 4) = raw4427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2192 raw4427; decide +kernel
    rw [heq]
    exact (canonical4427 hH).trans (sound1248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2192 (2 : Fin 4)) =
      Sparse.eval value1213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2192 (2 : Fin 4) = raw4422 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2192 raw4422; decide +kernel
    rw [heq]
    exact (canonical4422 hH).trans (sound1213 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2192 (3 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2192 (3 : Fin 4) = raw4421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2192 raw4421; decide +kernel
    rw [heq]
    exact (canonical4421 hH).trans (sound973 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2192 + (injectiveMoment H (mergeFirst pivotMatrix2192 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2192 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2192 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2192 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2192, value1213, value1247, value1248, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2193 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2193 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem sound2193 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2193 = Sparse.eval value2193 (momentVector H) := by
  have heq : pivotMatrix2193 = (fun u v => node2193 (pivotPermutation2193 u) v) := by apply Matrix.ext; unfold pivotMatrix2193 node2193 pivotPermutation2193; decide +kernel
  have hmoment : injectiveMoment H node2193 = injectiveMoment H pivotMatrix2193 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2193 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2193 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2193 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2193 (0 : Fin 4) = raw4622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2193 raw4622; decide +kernel
    rw [heq]
    exact (canonical4622 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2193 (1 : Fin 4)) =
      Sparse.eval value1067 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2193 (1 : Fin 4) = raw4430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2193 raw4430; decide +kernel
    rw [heq]
    exact (canonical4430 hH).trans (sound1067 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2193 (2 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2193 (2 : Fin 4) = raw4427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2193 raw4427; decide +kernel
    rw [heq]
    exact (canonical4427 hH).trans (sound1248 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2193 (3 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2193 (3 : Fin 4) = raw4426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2193 raw4426; decide +kernel
    rw [heq]
    exact (canonical4426 hH).trans (sound815 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2193 + (injectiveMoment H (mergeFirst pivotMatrix2193 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2193 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2193 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2193 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2193, value1058, value1067, value1248, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2194 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2194 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem sound2194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2194 = Sparse.eval value2194 (momentVector H) := by
  have heq : pivotMatrix2194 = (fun u v => node2194 (pivotPermutation2194 u) v) := by apply Matrix.ext; unfold pivotMatrix2194 node2194 pivotPermutation2194; decide +kernel
  have hmoment : injectiveMoment H node2194 = injectiveMoment H pivotMatrix2194 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2194 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2194 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2194 (0 : Fin 4)) =
      Sparse.eval value514 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2194 (0 : Fin 4) = raw4624 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2194 raw4624; decide +kernel
    rw [heq]
    exact (canonical4624 hH).trans (sound514 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2194 (1 : Fin 4)) =
      Sparse.eval value677 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2194 (1 : Fin 4) = raw4431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2194 raw4431; decide +kernel
    rw [heq]
    exact (canonical4431 hH).trans (sound677 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2194 (2 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2194 (2 : Fin 4) = raw4429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2194 raw4429; decide +kernel
    rw [heq]
    exact (canonical4429 hH).trans (sound995 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2194 (3 : Fin 4)) =
      Sparse.eval value676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2194 (3 : Fin 4) = raw4428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2194 raw4428; decide +kernel
    rw [heq]
    exact (canonical4428 hH).trans (sound676 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2194 + (injectiveMoment H (mergeFirst pivotMatrix2194 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2194 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2194 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2194 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2194, value514, value676, value677, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2195 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2195 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound2195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2195 = Sparse.eval value2195 (momentVector H) := by
  have heq : pivotMatrix2195 = (fun u v => node2195 (pivotPermutation2195 u) v) := by apply Matrix.ext; unfold pivotMatrix2195 node2195 pivotPermutation2195; decide +kernel
  have hmoment : injectiveMoment H node2195 = injectiveMoment H pivotMatrix2195 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2195 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2195 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2195 (0 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2195 (0 : Fin 4) = raw4627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2195 raw4627; decide +kernel
    rw [heq]
    exact (canonical4627 hH).trans (sound1013 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2195 (1 : Fin 4)) =
      Sparse.eval value1019 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2195 (1 : Fin 4) = raw4434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2195 raw4434; decide +kernel
    rw [heq]
    exact (canonical4434 hH).trans (sound1019 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2195 (2 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2195 (2 : Fin 4) = raw4432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2195 raw4432; decide +kernel
    rw [heq]
    exact (canonical4432 hH).trans (sound1028 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2195 (3 : Fin 4)) =
      Sparse.eval value677 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2195 (3 : Fin 4) = raw4431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2195 raw4431; decide +kernel
    rw [heq]
    exact (canonical4431 hH).trans (sound677 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2195 + (injectiveMoment H (mergeFirst pivotMatrix2195 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2195 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2195 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2195 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2195, value1013, value1019, value1028, value677, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2196 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2196 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

theorem sound2196 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2196 = Sparse.eval value2196 (momentVector H) := by
  have heq : pivotMatrix2196 = (fun u v => node2196 (pivotPermutation2196 u) v) := by apply Matrix.ext; unfold pivotMatrix2196 node2196 pivotPermutation2196; decide +kernel
  have hmoment : injectiveMoment H node2196 = injectiveMoment H pivotMatrix2196 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2196 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2196 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2196 (0 : Fin 4)) =
      Sparse.eval value794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2196 (0 : Fin 4) = raw5229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2196 raw5229; decide +kernel
    rw [heq]
    exact (canonical5229 hH).trans (sound794 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2196 (1 : Fin 4)) =
      Sparse.eval value815 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2196 (1 : Fin 4) = raw4426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2196 raw4426; decide +kernel
    rw [heq]
    exact (canonical4426 hH).trans (sound815 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2196 (2 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2196 (2 : Fin 4) = raw4401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2196 raw4401; decide +kernel
    rw [heq]
    exact (canonical4401 hH).trans (sound1032 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2196 (3 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2196 (3 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2196 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2196 + (injectiveMoment H (mergeFirst pivotMatrix2196 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2196 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2196 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2196 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2196, value1032, value484, value794, value815, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2197 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2197 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound2197 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2197 = Sparse.eval value2197 (momentVector H) := by
  have heq : pivotMatrix2197 = (fun u v => node2197 (pivotPermutation2197 u) v) := by apply Matrix.ext; unfold pivotMatrix2197 node2197 pivotPermutation2197; decide +kernel
  have hmoment : injectiveMoment H node2197 = injectiveMoment H pivotMatrix2197 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2197 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2197 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2197 (0 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2197 (0 : Fin 4) = raw5230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2197 raw5230; decide +kernel
    rw [heq]
    exact (canonical5230 hH).trans (sound991 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2197 (1 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2197 (1 : Fin 4) = raw4429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2197 raw4429; decide +kernel
    rw [heq]
    exact (canonical4429 hH).trans (sound995 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2197 (2 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2197 (2 : Fin 4) = raw4403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2197 raw4403; decide +kernel
    rw [heq]
    exact (canonical4403 hH).trans (sound1083 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2197 (3 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2197 (3 : Fin 4) = raw4401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2197 raw4401; decide +kernel
    rw [heq]
    exact (canonical4401 hH).trans (sound1032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2197 + (injectiveMoment H (mergeFirst pivotMatrix2197 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2197 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2197 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2197 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2197, value1032, value1083, value991, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2198 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2198 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem sound2198 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2198 = Sparse.eval value2198 (momentVector H) := by
  have heq : pivotMatrix2198 = (fun u v => node2198 (pivotPermutation2198 u) v) := by apply Matrix.ext; unfold pivotMatrix2198 node2198 pivotPermutation2198; decide +kernel
  have hmoment : injectiveMoment H node2198 = injectiveMoment H pivotMatrix2198 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2198 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2198 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2198 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2198 (0 : Fin 4) = raw5297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2198 raw5297; decide +kernel
    rw [heq]
    exact (canonical5297 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2198 (1 : Fin 4)) =
      Sparse.eval value1067 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2198 (1 : Fin 4) = raw4430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2198 raw4430; decide +kernel
    rw [heq]
    exact (canonical4430 hH).trans (sound1067 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2198 (2 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2198 (2 : Fin 4) = raw4402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2198 raw4402; decide +kernel
    rw [heq]
    exact (canonical4402 hH).trans (sound1083 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2198 (3 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2198 (3 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2198 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2198 + (injectiveMoment H (mergeFirst pivotMatrix2198 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2198 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2198 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2198 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2198, value1059, value1067, value1083, value484, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2199 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2199 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem sound2199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2199 = Sparse.eval value2199 (momentVector H) := by
  have heq : pivotMatrix2199 = (fun u v => node2199 (pivotPermutation2199 u) v) := by apply Matrix.ext; unfold pivotMatrix2199 node2199 pivotPermutation2199; decide +kernel
  have hmoment : injectiveMoment H node2199 = injectiveMoment H pivotMatrix2199 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2199 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2199 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2199 (0 : Fin 4)) =
      Sparse.eval value1222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2199 (0 : Fin 4) = raw7104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2199 raw7104; decide +kernel
    rw [heq]
    exact (canonical7104 hH).trans (sound1222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2199 (1 : Fin 4)) =
      Sparse.eval value676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2199 (1 : Fin 4) = raw4437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2199 raw4437; decide +kernel
    rw [heq]
    exact (canonical4437 hH).trans (sound676 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2199 (2 : Fin 4)) =
      Sparse.eval value1351 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2199 (2 : Fin 4) = raw4404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2199 raw4404; decide +kernel
    rw [heq]
    exact (canonical4404 hH).trans (sound1351 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2199 (3 : Fin 4)) =
      Sparse.eval value407 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2199 (3 : Fin 4) = raw4397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2199 raw4397; decide +kernel
    rw [heq]
    exact (canonical4397 hH).trans (sound407 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2199 + (injectiveMoment H (mergeFirst pivotMatrix2199 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2199 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2199 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2199 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2199, value1222, value1351, value407, value676, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2200 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2200 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound2200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2200 = Sparse.eval value2200 (momentVector H) := by
  have heq : pivotMatrix2200 = (fun u v => node2200 (pivotPermutation2200 u) v) := by apply Matrix.ext; unfold pivotMatrix2200 node2200 pivotPermutation2200; decide +kernel
  have hmoment : injectiveMoment H node2200 = injectiveMoment H pivotMatrix2200 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2200 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2200 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2200 (0 : Fin 4)) =
      Sparse.eval value1021 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2200 (0 : Fin 4) = raw5232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2200 raw5232; decide +kernel
    rw [heq]
    exact (canonical5232 hH).trans (sound1021 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2200 (1 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2200 (1 : Fin 4) = raw4432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2200 raw4432; decide +kernel
    rw [heq]
    exact (canonical4432 hH).trans (sound1028 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2200 (2 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2200 (2 : Fin 4) = raw4413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2200 raw4413; decide +kernel
    rw [heq]
    exact (canonical4413 hH).trans (sound1062 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2200 (3 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2200 (3 : Fin 4) = raw4412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2200 raw4412; decide +kernel
    rw [heq]
    exact (canonical4412 hH).trans (sound1062 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2200 + (injectiveMoment H (mergeFirst pivotMatrix2200 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2200 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2200 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2200 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2200, value1021, value1028, value1062, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2201 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2201 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound2201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2201 = Sparse.eval value2201 (momentVector H) := by
  have heq : pivotMatrix2201 = (fun u v => node2201 (pivotPermutation2201 u) v) := by apply Matrix.ext; unfold pivotMatrix2201 node2201 pivotPermutation2201; decide +kernel
  have hmoment : injectiveMoment H node2201 = injectiveMoment H pivotMatrix2201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2201 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2201 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2201 (0 : Fin 4)) =
      Sparse.eval value1012 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2201 (0 : Fin 4) = raw5301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2201 raw5301; decide +kernel
    rw [heq]
    exact (canonical5301 hH).trans (sound1012 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2201 (1 : Fin 4)) =
      Sparse.eval value1019 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2201 (1 : Fin 4) = raw4434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2201 raw4434; decide +kernel
    rw [heq]
    exact (canonical4434 hH).trans (sound1019 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2201 (2 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2201 (2 : Fin 4) = raw4413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2201 raw4413; decide +kernel
    rw [heq]
    exact (canonical4413 hH).trans (sound1062 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2201 (3 : Fin 4)) =
      Sparse.eval value1072 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2201 (3 : Fin 4) = raw4411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2201 raw4411; decide +kernel
    rw [heq]
    exact (canonical4411 hH).trans (sound1072 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2201 + (injectiveMoment H (mergeFirst pivotMatrix2201 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2201 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2201 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2201 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2201, value1012, value1019, value1062, value1072, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2202 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2202 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2202 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2202 = Sparse.eval value2202 (momentVector H) := by
  have heq : pivotMatrix2202 = (fun u v => node2202 (pivotPermutation2202 u) v) := by apply Matrix.ext; unfold pivotMatrix2202 node2202 pivotPermutation2202; decide +kernel
  have hmoment : injectiveMoment H node2202 = injectiveMoment H pivotMatrix2202 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2202 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2202 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2202 (0 : Fin 4)) =
      Sparse.eval value1014 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2202 (0 : Fin 4) = raw5243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2202 raw5243; decide +kernel
    rw [heq]
    exact (canonical5243 hH).trans (sound1014 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2202 (1 : Fin 4)) =
      Sparse.eval value1295 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2202 (1 : Fin 4) = raw4502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2202 raw4502; decide +kernel
    rw [heq]
    exact (canonical4502 hH).trans (sound1295 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2202 (2 : Fin 4)) =
      Sparse.eval value940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2202 (2 : Fin 4) = raw4452 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2202 raw4452; decide +kernel
    rw [heq]
    exact (canonical4452 hH).trans (sound940 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2202 (3 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2202 (3 : Fin 4) = raw4451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2202 raw4451; decide +kernel
    rw [heq]
    exact (canonical4451 hH).trans (sound1100 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2202 + (injectiveMoment H (mergeFirst pivotMatrix2202 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2202 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2202 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2202 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2202, value1014, value1100, value1295, value940, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2203 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2203 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem sound2203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2203 = Sparse.eval value2203 (momentVector H) := by
  have heq : pivotMatrix2203 = (fun u v => node2203 (pivotPermutation2203 u) v) := by apply Matrix.ext; unfold pivotMatrix2203 node2203 pivotPermutation2203; decide +kernel
  have hmoment : injectiveMoment H node2203 = injectiveMoment H pivotMatrix2203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2203 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2203 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2203 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (0 : Fin 4) = raw7169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw7169; decide +kernel
    rw [heq]
    exact (canonical7169 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2203 (1 : Fin 4)) =
      Sparse.eval value927 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (1 : Fin 4) = raw4632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw4632; decide +kernel
    rw [heq]
    exact (canonical4632 hH).trans (sound927 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2203 (2 : Fin 4)) =
      Sparse.eval value940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (2 : Fin 4) = raw4453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw4453; decide +kernel
    rw [heq]
    exact (canonical4453 hH).trans (sound940 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2203 (3 : Fin 4)) =
      Sparse.eval value578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (3 : Fin 4) = raw4450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw4450; decide +kernel
    rw [heq]
    exact (canonical4450 hH).trans (sound578 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2203 + (injectiveMoment H (mergeFirst pivotMatrix2203 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2203 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2203 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2203 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2203, value1168, value578, value927, value940, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2204 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2204 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound2204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2204 = Sparse.eval value2204 (momentVector H) := by
  have heq : pivotMatrix2204 = (fun u v => node2204 (pivotPermutation2204 u) v) := by apply Matrix.ext; unfold pivotMatrix2204 node2204 pivotPermutation2204; decide +kernel
  have hmoment : injectiveMoment H node2204 = injectiveMoment H pivotMatrix2204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2204 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2204 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2204 (0 : Fin 4) = raw3544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2204 raw3544; decide +kernel
    rw [heq]
    exact (canonical3544 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2204 (1 : Fin 4)) =
      Sparse.eval value1362 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2204 (1 : Fin 4) = raw4540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2204 raw4540; decide +kernel
    rw [heq]
    exact (canonical4540 hH).trans (sound1362 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2204 (2 : Fin 4)) =
      Sparse.eval value684 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2204 (2 : Fin 4) = raw4608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2204 raw4608; decide +kernel
    rw [heq]
    exact (canonical4608 hH).trans (sound684 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2204 (3 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2204 (3 : Fin 4) = raw4611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2204 raw4611; decide +kernel
    rw [heq]
    exact (canonical4611 hH).trans (sound685 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2204 + (injectiveMoment H (mergeFirst pivotMatrix2204 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2204 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2204 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2204 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2204, value1309, value1362, value684, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2205 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2205 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

theorem sound2205 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2205 = Sparse.eval value2205 (momentVector H) := by
  have heq : pivotMatrix2205 = (fun u v => node2205 (pivotPermutation2205 u) v) := by apply Matrix.ext; unfold pivotMatrix2205 node2205 pivotPermutation2205; decide +kernel
  have hmoment : injectiveMoment H node2205 = injectiveMoment H pivotMatrix2205 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2205 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2205 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2205 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2205 (0 : Fin 4) = raw7176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2205 raw7176; decide +kernel
    rw [heq]
    exact (canonical7176 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2205 (1 : Fin 4)) =
      Sparse.eval value682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2205 (1 : Fin 4) = raw4633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2205 raw4633; decide +kernel
    rw [heq]
    exact (canonical4633 hH).trans (sound682 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2205 (2 : Fin 4)) =
      Sparse.eval value679 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2205 (2 : Fin 4) = raw4474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2205 raw4474; decide +kernel
    rw [heq]
    exact (canonical4474 hH).trans (sound679 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2205 (3 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2205 (3 : Fin 4) = raw4464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2205 raw4464; decide +kernel
    rw [heq]
    exact (canonical4464 hH).trans (sound1315 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2205 + (injectiveMoment H (mergeFirst pivotMatrix2205 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2205 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2205 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2205 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2205, value1315, value679, value682, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2206 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2206 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound2206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2206 = Sparse.eval value2206 (momentVector H) := by
  have heq : pivotMatrix2206 = (fun u v => node2206 (pivotPermutation2206 u) v) := by apply Matrix.ext; unfold pivotMatrix2206 node2206 pivotPermutation2206; decide +kernel
  have hmoment : injectiveMoment H node2206 = injectiveMoment H pivotMatrix2206 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2206 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2206 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2206 (0 : Fin 4)) =
      Sparse.eval value673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2206 (0 : Fin 4) = raw4317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2206 raw4317; decide +kernel
    rw [heq]
    exact (canonical4317 hH).trans (sound673 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2206 (1 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2206 (1 : Fin 4) = raw4461 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2206 raw4461; decide +kernel
    rw [heq]
    exact (canonical4461 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2206 (2 : Fin 4)) =
      Sparse.eval value679 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2206 (2 : Fin 4) = raw4474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2206 raw4474; decide +kernel
    rw [heq]
    exact (canonical4474 hH).trans (sound679 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2206 (3 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2206 (3 : Fin 4) = raw4475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2206 raw4475; decide +kernel
    rw [heq]
    exact (canonical4475 hH).trans (sound517 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2206 + (injectiveMoment H (mergeFirst pivotMatrix2206 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2206 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2206 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2206 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2206, value1123, value517, value673, value679, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2207 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2207 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2207 = Sparse.eval value2207 (momentVector H) := by
  have heq : pivotMatrix2207 = (fun u v => node2207 (pivotPermutation2207 u) v) := by apply Matrix.ext; unfold pivotMatrix2207 node2207 pivotPermutation2207; decide +kernel
  have hmoment : injectiveMoment H node2207 = injectiveMoment H pivotMatrix2207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2207 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2207 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2207 (0 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2207 (0 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2207 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2207 (1 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2207 (1 : Fin 4) = raw4462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2207 raw4462; decide +kernel
    rw [heq]
    exact (canonical4462 hH).trans (sound1096 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2207 (2 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2207 (2 : Fin 4) = raw4476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2207 raw4476; decide +kernel
    rw [heq]
    exact (canonical4476 hH).trans (sound1078 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2207 (3 : Fin 4)) =
      Sparse.eval value522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2207 (3 : Fin 4) = raw4477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2207 raw4477; decide +kernel
    rw [heq]
    exact (canonical4477 hH).trans (sound522 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2207 + (injectiveMoment H (mergeFirst pivotMatrix2207 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2207 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2207 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2207 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2207, value1078, value1096, value502, value522, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2208 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2208 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem sound2208 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2208 = Sparse.eval value2208 (momentVector H) := by
  have heq : pivotMatrix2208 = (fun u v => node2208 (pivotPermutation2208 u) v) := by apply Matrix.ext; unfold pivotMatrix2208 node2208 pivotPermutation2208; decide +kernel
  have hmoment : injectiveMoment H node2208 = injectiveMoment H pivotMatrix2208 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2208 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2208 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2208 (0 : Fin 4)) =
      Sparse.eval value621 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2208 (0 : Fin 4) = raw4691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2208 raw4691; decide +kernel
    rw [heq]
    exact (canonical4691 hH).trans (sound621 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2208 (1 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2208 (1 : Fin 4) = raw4484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2208 raw4484; decide +kernel
    rw [heq]
    exact (canonical4484 hH).trans (sound680 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2208 (2 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2208 (2 : Fin 4) = raw4476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2208 raw4476; decide +kernel
    rw [heq]
    exact (canonical4476 hH).trans (sound1078 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2208 (3 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2208 (3 : Fin 4) = raw4475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2208 raw4475; decide +kernel
    rw [heq]
    exact (canonical4475 hH).trans (sound517 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2208 + (injectiveMoment H (mergeFirst pivotMatrix2208 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2208 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2208 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2208 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2208, value1078, value517, value621, value680, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2209 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2209 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2209 = Sparse.eval value2209 (momentVector H) := by
  have heq : pivotMatrix2209 = (fun u v => node2209 (pivotPermutation2209 u) v) := by apply Matrix.ext; unfold pivotMatrix2209 node2209 pivotPermutation2209; decide +kernel
  have hmoment : injectiveMoment H node2209 = injectiveMoment H pivotMatrix2209 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2209 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2209 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2209 (0 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2209 (0 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2209 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2209 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2209 (1 : Fin 4) = raw4476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2209 raw4476; decide +kernel
    rw [heq]
    exact (canonical4476 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2209 (2 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2209 (2 : Fin 4) = raw4484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2209 raw4484; decide +kernel
    rw [heq]
    exact (canonical4484 hH).trans (sound680 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2209 (3 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2209 (3 : Fin 4) = raw4485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2209 raw4485; decide +kernel
    rw [heq]
    exact (canonical4485 hH).trans (sound1056 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2209 + (injectiveMoment H (mergeFirst pivotMatrix2209 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2209 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2209 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2209 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2209, value1056, value1074, value1078, value680, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2210 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2210 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem sound2210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2210 = Sparse.eval value2210 (momentVector H) := by
  have heq : pivotMatrix2210 = (fun u v => node2210 (pivotPermutation2210 u) v) := by apply Matrix.ext; unfold pivotMatrix2210 node2210 pivotPermutation2210; decide +kernel
  have hmoment : injectiveMoment H node2210 = injectiveMoment H pivotMatrix2210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2210 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2210 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2210 (0 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2210 (0 : Fin 4) = raw7182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2210 raw7182; decide +kernel
    rw [heq]
    exact (canonical7182 hH).trans (sound1206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2210 (1 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2210 (1 : Fin 4) = raw4634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2210 raw4634; decide +kernel
    rw [heq]
    exact (canonical4634 hH).trans (sound1310 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2210 (2 : Fin 4)) =
      Sparse.eval value1049 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2210 (2 : Fin 4) = raw4486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2210 raw4486; decide +kernel
    rw [heq]
    exact (canonical4486 hH).trans (sound1049 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2210 (3 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2210 (3 : Fin 4) = raw4479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2210 raw4479; decide +kernel
    rw [heq]
    exact (canonical4479 hH).trans (sound603 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2210 + (injectiveMoment H (mergeFirst pivotMatrix2210 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2210 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2210 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2210 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2210, value1049, value1206, value1310, value603, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2211 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2211 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound2211 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2211 = Sparse.eval value2211 (momentVector H) := by
  have heq : pivotMatrix2211 = (fun u v => node2211 (pivotPermutation2211 u) v) := by apply Matrix.ext; unfold pivotMatrix2211 node2211 pivotPermutation2211; decide +kernel
  have hmoment : injectiveMoment H node2211 = injectiveMoment H pivotMatrix2211 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2211 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2211 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2211 (0 : Fin 4)) =
      Sparse.eval value1073 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2211 (0 : Fin 4) = raw5259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2211 raw5259; decide +kernel
    rw [heq]
    exact (canonical5259 hH).trans (sound1073 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2211 (1 : Fin 4)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2211 (1 : Fin 4) = raw4588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2211 raw4588; decide +kernel
    rw [heq]
    exact (canonical4588 hH).trans (sound837 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2211 (2 : Fin 4)) =
      Sparse.eval value1049 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2211 (2 : Fin 4) = raw4486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2211 raw4486; decide +kernel
    rw [heq]
    exact (canonical4486 hH).trans (sound1049 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2211 (3 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2211 (3 : Fin 4) = raw4484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2211 raw4484; decide +kernel
    rw [heq]
    exact (canonical4484 hH).trans (sound680 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2211 + (injectiveMoment H (mergeFirst pivotMatrix2211 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2211 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2211 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2211 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2211, value1049, value1073, value680, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2212 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2212 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound2212 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2212 = Sparse.eval value2212 (momentVector H) := by
  have heq : pivotMatrix2212 = (fun u v => node2212 (pivotPermutation2212 u) v) := by apply Matrix.ext; unfold pivotMatrix2212 node2212 pivotPermutation2212; decide +kernel
  have hmoment : injectiveMoment H node2212 = injectiveMoment H pivotMatrix2212 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2212 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2212 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2212 (0 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2212 (0 : Fin 4) = raw5314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2212 raw5314; decide +kernel
    rw [heq]
    exact (canonical5314 hH).trans (sound943 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2212 (1 : Fin 4)) =
      Sparse.eval value937 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2212 (1 : Fin 4) = raw4602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2212 raw4602; decide +kernel
    rw [heq]
    exact (canonical4602 hH).trans (sound937 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2212 (2 : Fin 4)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2212 (2 : Fin 4) = raw4487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2212 raw4487; decide +kernel
    rw [heq]
    exact (canonical4487 hH).trans (sound967 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2212 (3 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2212 (3 : Fin 4) = raw4484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2212 raw4484; decide +kernel
    rw [heq]
    exact (canonical4484 hH).trans (sound680 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2212 + (injectiveMoment H (mergeFirst pivotMatrix2212 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2212 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2212 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2212 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2212, value680, value937, value943, value967, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2213 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2213 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound2213 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2213 = Sparse.eval value2213 (momentVector H) := by
  have heq : pivotMatrix2213 = (fun u v => node2213 (pivotPermutation2213 u) v) := by apply Matrix.ext; unfold pivotMatrix2213 node2213 pivotPermutation2213; decide +kernel
  have hmoment : injectiveMoment H node2213 = injectiveMoment H pivotMatrix2213 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2213 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2213 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2213 (0 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2213 (0 : Fin 4) = raw5315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2213 raw5315; decide +kernel
    rw [heq]
    exact (canonical5315 hH).trans (sound1007 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2213 (1 : Fin 4)) =
      Sparse.eval value1015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2213 (1 : Fin 4) = raw4603 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2213 raw4603; decide +kernel
    rw [heq]
    exact (canonical4603 hH).trans (sound1015 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2213 (2 : Fin 4)) =
      Sparse.eval value1049 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2213 (2 : Fin 4) = raw4488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2213 raw4488; decide +kernel
    rw [heq]
    exact (canonical4488 hH).trans (sound1049 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2213 (3 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2213 (3 : Fin 4) = raw4485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2213 raw4485; decide +kernel
    rw [heq]
    exact (canonical4485 hH).trans (sound1056 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2213 + (injectiveMoment H (mergeFirst pivotMatrix2213 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2213 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2213 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2213 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2213, value1007, value1015, value1049, value1056, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2214 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2214 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound2214 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2214 = Sparse.eval value2214 (momentVector H) := by
  have heq : pivotMatrix2214 = (fun u v => node2214 (pivotPermutation2214 u) v) := by apply Matrix.ext; unfold pivotMatrix2214 node2214 pivotPermutation2214; decide +kernel
  have hmoment : injectiveMoment H node2214 = injectiveMoment H pivotMatrix2214 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2214 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2214 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2214 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2214 (0 : Fin 4) = raw4736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2214 raw4736; decide +kernel
    rw [heq]
    exact (canonical4736 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2214 (1 : Fin 4)) =
      Sparse.eval value1253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2214 (1 : Fin 4) = raw4529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2214 raw4529; decide +kernel
    rw [heq]
    exact (canonical4529 hH).trans (sound1253 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2214 (2 : Fin 4)) =
      Sparse.eval value681 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2214 (2 : Fin 4) = raw4496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2214 raw4496; decide +kernel
    rw [heq]
    exact (canonical4496 hH).trans (sound681 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2214 (3 : Fin 4)) =
      Sparse.eval value1266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2214 (3 : Fin 4) = raw4494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2214 raw4494; decide +kernel
    rw [heq]
    exact (canonical4494 hH).trans (sound1266 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2214 + (injectiveMoment H (mergeFirst pivotMatrix2214 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2214 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2214 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2214 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2214, value1059, value1253, value1266, value681, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2215 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2215 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem sound2215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2215 = Sparse.eval value2215 (momentVector H) := by
  have heq : pivotMatrix2215 = (fun u v => node2215 (pivotPermutation2215 u) v) := by apply Matrix.ext; unfold pivotMatrix2215 node2215 pivotPermutation2215; decide +kernel
  have hmoment : injectiveMoment H node2215 = injectiveMoment H pivotMatrix2215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2215 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2215 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2215 (0 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2215 (0 : Fin 4) = raw5328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2215 raw5328; decide +kernel
    rw [heq]
    exact (canonical5328 hH).trans (sound683 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2215 (1 : Fin 4)) =
      Sparse.eval value684 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2215 (1 : Fin 4) = raw4608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2215 raw4608; decide +kernel
    rw [heq]
    exact (canonical4608 hH).trans (sound684 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2215 (2 : Fin 4)) =
      Sparse.eval value1370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2215 (2 : Fin 4) = raw4503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2215 raw4503; decide +kernel
    rw [heq]
    exact (canonical4503 hH).trans (sound1370 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2215 (3 : Fin 4)) =
      Sparse.eval value682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2215 (3 : Fin 4) = raw4500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2215 raw4500; decide +kernel
    rw [heq]
    exact (canonical4500 hH).trans (sound682 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2215 + (injectiveMoment H (mergeFirst pivotMatrix2215 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2215 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2215 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2215 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2215, value1370, value682, value683, value684, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2216 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2216 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound2216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2216 = Sparse.eval value2216 (momentVector H) := by
  have heq : pivotMatrix2216 = (fun u v => node2216 (pivotPermutation2216 u) v) := by apply Matrix.ext; unfold pivotMatrix2216 node2216 pivotPermutation2216; decide +kernel
  have hmoment : injectiveMoment H node2216 = injectiveMoment H pivotMatrix2216 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2216 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2216 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2216 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (0 : Fin 4) = raw5329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw5329; decide +kernel
    rw [heq]
    exact (canonical5329 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2216 (1 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (1 : Fin 4) = raw4609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4609; decide +kernel
    rw [heq]
    exact (canonical4609 hH).trans (sound1310 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2216 (2 : Fin 4)) =
      Sparse.eval value1317 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (2 : Fin 4) = raw4504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4504; decide +kernel
    rw [heq]
    exact (canonical4504 hH).trans (sound1317 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2216 (3 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (3 : Fin 4) = raw4501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4501; decide +kernel
    rw [heq]
    exact (canonical4501 hH).trans (sound593 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2216 + (injectiveMoment H (mergeFirst pivotMatrix2216 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2216, value1310, value1315, value1317, value593, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2217 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2217 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem sound2217 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2217 = Sparse.eval value2217 (momentVector H) := by
  have heq : pivotMatrix2217 = (fun u v => node2217 (pivotPermutation2217 u) v) := by apply Matrix.ext; unfold pivotMatrix2217 node2217 pivotPermutation2217; decide +kernel
  have hmoment : injectiveMoment H node2217 = injectiveMoment H pivotMatrix2217 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2217 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2217 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2217 (0 : Fin 4)) =
      Sparse.eval value1346 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2217 (0 : Fin 4) = raw7845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2217 raw7845; decide +kernel
    rw [heq]
    exact (canonical7845 hH).trans (sound1346 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2217 (1 : Fin 4)) =
      Sparse.eval value686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2217 (1 : Fin 4) = raw4638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2217 raw4638; decide +kernel
    rw [heq]
    exact (canonical4638 hH).trans (sound686 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2217 (2 : Fin 4)) =
      Sparse.eval value682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2217 (2 : Fin 4) = raw4506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2217 raw4506; decide +kernel
    rw [heq]
    exact (canonical4506 hH).trans (sound682 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2217 (3 : Fin 4)) =
      Sparse.eval value681 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2217 (3 : Fin 4) = raw4496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2217 raw4496; decide +kernel
    rw [heq]
    exact (canonical4496 hH).trans (sound681 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2217 + (injectiveMoment H (mergeFirst pivotMatrix2217 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2217 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2217 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2217 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2217, value1346, value681, value682, value686, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2218 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2218 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2218 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2218 = Sparse.eval value2218 (momentVector H) := by
  have heq : pivotMatrix2218 = (fun u v => node2218 (pivotPermutation2218 u) v) := by apply Matrix.ext; unfold pivotMatrix2218 node2218 pivotPermutation2218; decide +kernel
  have hmoment : injectiveMoment H node2218 = injectiveMoment H pivotMatrix2218 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2218 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2218 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2218 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2218 (0 : Fin 4) = raw7189 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2218 raw7189; decide +kernel
    rw [heq]
    exact (canonical7189 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2218 (1 : Fin 4)) =
      Sparse.eval value1089 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2218 (1 : Fin 4) = raw4635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2218 raw4635; decide +kernel
    rw [heq]
    exact (canonical4635 hH).trans (sound1089 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2218 (2 : Fin 4)) =
      Sparse.eval value1295 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2218 (2 : Fin 4) = raw4505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2218 raw4505; decide +kernel
    rw [heq]
    exact (canonical4505 hH).trans (sound1295 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2218 (3 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2218 (3 : Fin 4) = raw4498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2218 raw4498; decide +kernel
    rw [heq]
    exact (canonical4498 hH).trans (sound576 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2218 + (injectiveMoment H (mergeFirst pivotMatrix2218 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2218 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2218 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2218 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2218, value1089, value1178, value1295, value576, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2219 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2219 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem sound2219 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2219 = Sparse.eval value2219 (momentVector H) := by
  have heq : pivotMatrix2219 = (fun u v => node2219 (pivotPermutation2219 u) v) := by apply Matrix.ext; unfold pivotMatrix2219 node2219 pivotPermutation2219; decide +kernel
  have hmoment : injectiveMoment H node2219 = injectiveMoment H pivotMatrix2219 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2219 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2219 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2219 (0 : Fin 4)) =
      Sparse.eval value1163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (0 : Fin 4) = raw4343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4343; decide +kernel
    rw [heq]
    exact (canonical4343 hH).trans (sound1163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2219 (1 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (1 : Fin 4) = raw4498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4498; decide +kernel
    rw [heq]
    exact (canonical4498 hH).trans (sound576 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2219 (2 : Fin 4)) =
      Sparse.eval value1190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (2 : Fin 4) = raw4531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4531; decide +kernel
    rw [heq]
    exact (canonical4531 hH).trans (sound1190 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2219 (3 : Fin 4)) =
      Sparse.eval value757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2219 (3 : Fin 4) = raw4534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2219 raw4534; decide +kernel
    rw [heq]
    exact (canonical4534 hH).trans (sound757 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2219 + (injectiveMoment H (mergeFirst pivotMatrix2219 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2219 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2219 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2219 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2219, value1163, value1190, value576, value757, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2220 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2220 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem sound2220 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2220 = Sparse.eval value2220 (momentVector H) := by
  have heq : pivotMatrix2220 = (fun u v => node2220 (pivotPermutation2220 u) v) := by apply Matrix.ext; unfold pivotMatrix2220 node2220 pivotPermutation2220; decide +kernel
  have hmoment : injectiveMoment H node2220 = injectiveMoment H pivotMatrix2220 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2220 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2220 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2220 (0 : Fin 4)) =
      Sparse.eval value1172 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (0 : Fin 4) = raw4344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4344; decide +kernel
    rw [heq]
    exact (canonical4344 hH).trans (sound1172 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2220 (1 : Fin 4)) =
      Sparse.eval value579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (1 : Fin 4) = raw4499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4499; decide +kernel
    rw [heq]
    exact (canonical4499 hH).trans (sound579 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2220 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (2 : Fin 4) = raw4535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4535; decide +kernel
    rw [heq]
    exact (canonical4535 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2220 (3 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (3 : Fin 4) = raw4536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4536; decide +kernel
    rw [heq]
    exact (canonical4536 hH).trans (sound1208 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2220 + (injectiveMoment H (mergeFirst pivotMatrix2220 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2220 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2220 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2220 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2220, value1172, value1208, value579, value896, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2221 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2221 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

theorem sound2221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2221 = Sparse.eval value2221 (momentVector H) := by
  have heq : pivotMatrix2221 = (fun u v => node2221 (pivotPermutation2221 u) v) := by apply Matrix.ext; unfold pivotMatrix2221 node2221 pivotPermutation2221; decide +kernel
  have hmoment : injectiveMoment H node2221 = injectiveMoment H pivotMatrix2221 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2221 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2221 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2221 (0 : Fin 4)) =
      Sparse.eval value1372 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2221 (0 : Fin 4) = raw4345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2221 raw4345; decide +kernel
    rw [heq]
    exact (canonical4345 hH).trans (sound1372 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2221 (1 : Fin 4)) =
      Sparse.eval value682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2221 (1 : Fin 4) = raw4500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2221 raw4500; decide +kernel
    rw [heq]
    exact (canonical4500 hH).trans (sound682 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2221 (2 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2221 (2 : Fin 4) = raw4536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2221 raw4536; decide +kernel
    rw [heq]
    exact (canonical4536 hH).trans (sound1208 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2221 (3 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2221 (3 : Fin 4) = raw4537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2221 raw4537; decide +kernel
    rw [heq]
    exact (canonical4537 hH).trans (sound1276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2221 + (injectiveMoment H (mergeFirst pivotMatrix2221 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2221 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2221 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2221 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2221, value1208, value1276, value1372, value682, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2222 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2222 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem sound2222 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2222 = Sparse.eval value2222 (momentVector H) := by
  have heq : pivotMatrix2222 = (fun u v => node2222 (pivotPermutation2222 u) v) := by apply Matrix.ext; unfold pivotMatrix2222 node2222 pivotPermutation2222; decide +kernel
  have hmoment : injectiveMoment H node2222 = injectiveMoment H pivotMatrix2222 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2222 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2222 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2222 (0 : Fin 4)) =
      Sparse.eval value1219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2222 (0 : Fin 4) = raw4369 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2222 raw4369; decide +kernel
    rw [heq]
    exact (canonical4369 hH).trans (sound1219 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2222 (1 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2222 (1 : Fin 4) = raw4545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2222 raw4545; decide +kernel
    rw [heq]
    exact (canonical4545 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2222 (2 : Fin 4)) =
      Sparse.eval value1370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2222 (2 : Fin 4) = raw4560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2222 raw4560; decide +kernel
    rw [heq]
    exact (canonical4560 hH).trans (sound1370 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2222 (3 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2222 (3 : Fin 4) = raw4564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2222 raw4564; decide +kernel
    rw [heq]
    exact (canonical4564 hH).trans (sound1263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2222 + (injectiveMoment H (mergeFirst pivotMatrix2222 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2222 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2222 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2222 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2222, value1219, value1263, value1370, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2223 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2223 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

theorem sound2223 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2223 = Sparse.eval value2223 (momentVector H) := by
  have heq : pivotMatrix2223 = (fun u v => node2223 (pivotPermutation2223 u) v) := by apply Matrix.ext; unfold pivotMatrix2223 node2223 pivotPermutation2223; decide +kernel
  have hmoment : injectiveMoment H node2223 = injectiveMoment H pivotMatrix2223 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2223 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2223 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2223 (0 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2223 (0 : Fin 4) = raw4383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2223 raw4383; decide +kernel
    rw [heq]
    exact (canonical4383 hH).trans (sound983 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2223 (1 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2223 (1 : Fin 4) = raw4548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2223 raw4548; decide +kernel
    rw [heq]
    exact (canonical4548 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2223 (2 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2223 (2 : Fin 4) = raw4571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2223 raw4571; decide +kernel
    rw [heq]
    exact (canonical4571 hH).trans (sound1078 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2223 (3 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2223 (3 : Fin 4) = raw4572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2223 raw4572; decide +kernel
    rw [heq]
    exact (canonical4572 hH).trans (sound1276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2223 + (injectiveMoment H (mergeFirst pivotMatrix2223 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2223 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2223 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2223 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2223, value1078, value1276, value276, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2224 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2224 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem sound2224 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2224 = Sparse.eval value2224 (momentVector H) := by
  have heq : pivotMatrix2224 = (fun u v => node2224 (pivotPermutation2224 u) v) := by apply Matrix.ext; unfold pivotMatrix2224 node2224 pivotPermutation2224; decide +kernel
  have hmoment : injectiveMoment H node2224 = injectiveMoment H pivotMatrix2224 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2224 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2224 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2224 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2224 (0 : Fin 4) = raw4391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2224 raw4391; decide +kernel
    rw [heq]
    exact (canonical4391 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2224 (1 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2224 (1 : Fin 4) = raw4564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2224 raw4564; decide +kernel
    rw [heq]
    exact (canonical4564 hH).trans (sound1263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2224 (2 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2224 (2 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2224 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2224 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2224 (3 : Fin 4) = raw4580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2224 raw4580; decide +kernel
    rw [heq]
    exact (canonical4580 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2224 + (injectiveMoment H (mergeFirst pivotMatrix2224 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2224 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2224 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2224 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2224, value1263, value1314, value1315, value683, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2225 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2225 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem sound2225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2225 = Sparse.eval value2225 (momentVector H) := by
  have heq : pivotMatrix2225 = (fun u v => node2225 (pivotPermutation2225 u) v) := by apply Matrix.ext; unfold pivotMatrix2225 node2225 pivotPermutation2225; decide +kernel
  have hmoment : injectiveMoment H node2225 = injectiveMoment H pivotMatrix2225 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2225 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2225 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2225 (0 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2225 (0 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2225 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2225 (1 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2225 (1 : Fin 4) = raw4571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2225 raw4571; decide +kernel
    rw [heq]
    exact (canonical4571 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2225 (2 : Fin 4)) =
      Sparse.eval value510 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2225 (2 : Fin 4) = raw4586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2225 raw4586; decide +kernel
    rw [heq]
    exact (canonical4586 hH).trans (sound510 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2225 (3 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2225 (3 : Fin 4) = raw4587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2225 raw4587; decide +kernel
    rw [heq]
    exact (canonical4587 hH).trans (sound520 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2225 + (injectiveMoment H (mergeFirst pivotMatrix2225 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2225 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2225 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2225 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2225, value1078, value484, value510, value520, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2226 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2226 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem sound2226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2226 = Sparse.eval value2226 (momentVector H) := by
  have heq : pivotMatrix2226 = (fun u v => node2226 (pivotPermutation2226 u) v) := by apply Matrix.ext; unfold pivotMatrix2226 node2226 pivotPermutation2226; decide +kernel
  have hmoment : injectiveMoment H node2226 = injectiveMoment H pivotMatrix2226 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2226 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2226 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2226 (0 : Fin 4)) =
      Sparse.eval value1230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2226 (0 : Fin 4) = raw4414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2226 raw4414; decide +kernel
    rw [heq]
    exact (canonical4414 hH).trans (sound1230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2226 (1 : Fin 4)) =
      Sparse.eval value596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2226 (1 : Fin 4) = raw4607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2226 raw4607; decide +kernel
    rw [heq]
    exact (canonical4607 hH).trans (sound596 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2226 (2 : Fin 4)) =
      Sparse.eval value927 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2226 (2 : Fin 4) = raw4613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2226 raw4613; decide +kernel
    rw [heq]
    exact (canonical4613 hH).trans (sound927 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2226 (3 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2226 (3 : Fin 4) = raw4614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2226 raw4614; decide +kernel
    rw [heq]
    exact (canonical4614 hH).trans (sound1277 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2226 + (injectiveMoment H (mergeFirst pivotMatrix2226 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2226 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2226 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2226 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2226, value1230, value1277, value596, value927, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2227 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2227 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem sound2227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2227 = Sparse.eval value2227 (momentVector H) := by
  have heq : pivotMatrix2227 = (fun u v => node2227 (pivotPermutation2227 u) v) := by apply Matrix.ext; unfold pivotMatrix2227 node2227 pivotPermutation2227; decide +kernel
  have hmoment : injectiveMoment H node2227 = injectiveMoment H pivotMatrix2227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2227 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2227 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2227 (0 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2227 (0 : Fin 4) = raw4416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2227 raw4416; decide +kernel
    rw [heq]
    exact (canonical4416 hH).trans (sound1310 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2227 (1 : Fin 4)) =
      Sparse.eval value684 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2227 (1 : Fin 4) = raw4608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2227 raw4608; decide +kernel
    rw [heq]
    exact (canonical4608 hH).trans (sound684 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2227 (2 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2227 (2 : Fin 4) = raw4615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2227 raw4615; decide +kernel
    rw [heq]
    exact (canonical4615 hH).trans (sound1309 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2227 (3 : Fin 4)) =
      Sparse.eval value1244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2227 (3 : Fin 4) = raw4616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2227 raw4616; decide +kernel
    rw [heq]
    exact (canonical4616 hH).trans (sound1244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2227 + (injectiveMoment H (mergeFirst pivotMatrix2227 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2227 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2227 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2227 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2227, value1244, value1309, value1310, value684, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2228 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2228 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound2228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2228 = Sparse.eval value2228 (momentVector H) := by
  have heq : pivotMatrix2228 = (fun u v => node2228 (pivotPermutation2228 u) v) := by apply Matrix.ext; unfold pivotMatrix2228 node2228 pivotPermutation2228; decide +kernel
  have hmoment : injectiveMoment H node2228 = injectiveMoment H pivotMatrix2228 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2228 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2228 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2228 (0 : Fin 4)) =
      Sparse.eval value1224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2228 (0 : Fin 4) = raw4418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2228 raw4418; decide +kernel
    rw [heq]
    exact (canonical4418 hH).trans (sound1224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2228 (1 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2228 (1 : Fin 4) = raw4610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2228 raw4610; decide +kernel
    rw [heq]
    exact (canonical4610 hH).trans (sound1308 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2228 (2 : Fin 4)) =
      Sparse.eval value984 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2228 (2 : Fin 4) = raw4617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2228 raw4617; decide +kernel
    rw [heq]
    exact (canonical4617 hH).trans (sound984 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2228 (3 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2228 (3 : Fin 4) = raw4618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2228 raw4618; decide +kernel
    rw [heq]
    exact (canonical4618 hH).trans (sound1263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2228 + (injectiveMoment H (mergeFirst pivotMatrix2228 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2228 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2228 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2228 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2228, value1224, value1263, value1308, value984, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2229 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2229 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem sound2229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2229 = Sparse.eval value2229 (momentVector H) := by
  have heq : pivotMatrix2229 = (fun u v => node2229 (pivotPermutation2229 u) v) := by apply Matrix.ext; unfold pivotMatrix2229 node2229 pivotPermutation2229; decide +kernel
  have hmoment : injectiveMoment H node2229 = injectiveMoment H pivotMatrix2229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2229 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2229 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2229 (0 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2229 (0 : Fin 4) = raw4427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2229 raw4427; decide +kernel
    rw [heq]
    exact (canonical4427 hH).trans (sound1248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2229 (1 : Fin 4)) =
      Sparse.eval value1247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2229 (1 : Fin 4) = raw4620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2229 raw4620; decide +kernel
    rw [heq]
    exact (canonical4620 hH).trans (sound1247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2229 (2 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2229 (2 : Fin 4) = raw4622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2229 raw4622; decide +kernel
    rw [heq]
    exact (canonical4622 hH).trans (sound1058 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2229 (3 : Fin 4)) =
      Sparse.eval value686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2229 (3 : Fin 4) = raw4623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2229 raw4623; decide +kernel
    rw [heq]
    exact (canonical4623 hH).trans (sound686 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2229 + (injectiveMoment H (mergeFirst pivotMatrix2229 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2229 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2229 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2229 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2229, value1058, value1247, value1248, value686, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2230 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2230 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem sound2230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2230 = Sparse.eval value2230 (momentVector H) := by
  have heq : pivotMatrix2230 = (fun u v => node2230 (pivotPermutation2230 u) v) := by apply Matrix.ext; unfold pivotMatrix2230 node2230 pivotPermutation2230; decide +kernel
  have hmoment : injectiveMoment H node2230 = injectiveMoment H pivotMatrix2230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2230 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2230 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2230 (0 : Fin 4)) =
      Sparse.eval value1020 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2230 (0 : Fin 4) = raw4433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2230 raw4433; decide +kernel
    rw [heq]
    exact (canonical4433 hH).trans (sound1020 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2230 (1 : Fin 4)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2230 (1 : Fin 4) = raw4625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2230 raw4625; decide +kernel
    rw [heq]
    exact (canonical4625 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2230 (2 : Fin 4)) =
      Sparse.eval value927 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2230 (2 : Fin 4) = raw4628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2230 raw4628; decide +kernel
    rw [heq]
    exact (canonical4628 hH).trans (sound927 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2230 (3 : Fin 4)) =
      Sparse.eval value586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2230 (3 : Fin 4) = raw4629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2230 raw4629; decide +kernel
    rw [heq]
    exact (canonical4629 hH).trans (sound586 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2230 + (injectiveMoment H (mergeFirst pivotMatrix2230 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2230 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2230 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2230 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2230, value1016, value1020, value586, value927, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2231 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2231 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound2231 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2231 = Sparse.eval value2231 (momentVector H) := by
  have heq : pivotMatrix2231 = (fun u v => node2231 (pivotPermutation2231 u) v) := by apply Matrix.ext; unfold pivotMatrix2231 node2231 pivotPermutation2231; decide +kernel
  have hmoment : injectiveMoment H node2231 = injectiveMoment H pivotMatrix2231 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2231 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2231 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2231 (0 : Fin 4)) =
      Sparse.eval value1019 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2231 (0 : Fin 4) = raw4434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2231 raw4434; decide +kernel
    rw [heq]
    exact (canonical4434 hH).trans (sound1019 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2231 (1 : Fin 4)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2231 (1 : Fin 4) = raw4627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2231 raw4627; decide +kernel
    rw [heq]
    exact (canonical4627 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2231 (2 : Fin 4)) =
      Sparse.eval value1089 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2231 (2 : Fin 4) = raw4630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2231 raw4630; decide +kernel
    rw [heq]
    exact (canonical4630 hH).trans (sound1089 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2231 (3 : Fin 4)) =
      Sparse.eval value687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2231 (3 : Fin 4) = raw4631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2231 raw4631; decide +kernel
    rw [heq]
    exact (canonical4631 hH).trans (sound687 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2231 + (injectiveMoment H (mergeFirst pivotMatrix2231 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2231 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2231 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2231 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2231, value1013, value1019, value1089, value687, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2232 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2232 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem sound2232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2232 = Sparse.eval value2232 (momentVector H) := by
  have heq : pivotMatrix2232 = (fun u v => node2232 (pivotPermutation2232 u) v) := by apply Matrix.ext; unfold pivotMatrix2232 node2232 pivotPermutation2232; decide +kernel
  have hmoment : injectiveMoment H node2232 = injectiveMoment H pivotMatrix2232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2232 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2232 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2232 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2232 (0 : Fin 4) = raw4795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2232 raw4795; decide +kernel
    rw [heq]
    exact (canonical4795 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2232 (1 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2232 (1 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2232 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2232 (2 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2232 (2 : Fin 4) = raw4564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2232 raw4564; decide +kernel
    rw [heq]
    exact (canonical4564 hH).trans (sound1263 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2232 (3 : Fin 4)) =
      Sparse.eval value1370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2232 (3 : Fin 4) = raw4560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2232 raw4560; decide +kernel
    rw [heq]
    exact (canonical4560 hH).trans (sound1370 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2232 + (injectiveMoment H (mergeFirst pivotMatrix2232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2232, value1263, value1309, value1370, value683, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2233 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2233 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

theorem sound2233 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2233 = Sparse.eval value2233 (momentVector H) := by
  have heq : pivotMatrix2233 = (fun u v => node2233 (pivotPermutation2233 u) v) := by apply Matrix.ext; unfold pivotMatrix2233 node2233 pivotPermutation2233; decide +kernel
  have hmoment : injectiveMoment H node2233 = injectiveMoment H pivotMatrix2233 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2233 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2233 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2233 (0 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2233 (0 : Fin 4) = raw4799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2233 raw4799; decide +kernel
    rw [heq]
    exact (canonical4799 hH).trans (sound828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2233 (1 : Fin 4)) =
      Sparse.eval value410 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2233 (1 : Fin 4) = raw4585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2233 raw4585; decide +kernel
    rw [heq]
    exact (canonical4585 hH).trans (sound410 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2233 (2 : Fin 4)) =
      Sparse.eval value728 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2233 (2 : Fin 4) = raw4570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2233 raw4570; decide +kernel
    rw [heq]
    exact (canonical4570 hH).trans (sound728 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2233 (3 : Fin 4)) =
      Sparse.eval value842 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2233 (3 : Fin 4) = raw4569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2233 raw4569; decide +kernel
    rw [heq]
    exact (canonical4569 hH).trans (sound842 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2233 + (injectiveMoment H (mergeFirst pivotMatrix2233 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2233 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2233 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2233 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2233, value410, value728, value828, value842, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2234 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2234 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

theorem sound2234 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2234 = Sparse.eval value2234 (momentVector H) := by
  have heq : pivotMatrix2234 = (fun u v => node2234 (pivotPermutation2234 u) v) := by apply Matrix.ext; unfold pivotMatrix2234 node2234 pivotPermutation2234; decide +kernel
  have hmoment : injectiveMoment H node2234 = injectiveMoment H pivotMatrix2234 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2234 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2234 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2234 (0 : Fin 4)) =
      Sparse.eval value606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2234 (0 : Fin 4) = raw4810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2234 raw4810; decide +kernel
    rw [heq]
    exact (canonical4810 hH).trans (sound606 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2234 (1 : Fin 4)) =
      Sparse.eval value601 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2234 (1 : Fin 4) = raw4592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2234 raw4592; decide +kernel
    rw [heq]
    exact (canonical4592 hH).trans (sound601 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2234 (2 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2234 (2 : Fin 4) = raw4580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2234 raw4580; decide +kernel
    rw [heq]
    exact (canonical4580 hH).trans (sound1314 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2234 (3 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2234 (3 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2234 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2234 + (injectiveMoment H (mergeFirst pivotMatrix2234 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2234 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2234 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2234 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2234, value1314, value601, value606, value683, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2235 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2235 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

theorem sound2235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2235 = Sparse.eval value2235 (momentVector H) := by
  have heq : pivotMatrix2235 = (fun u v => node2235 (pivotPermutation2235 u) v) := by apply Matrix.ext; unfold pivotMatrix2235 node2235 pivotPermutation2235; decide +kernel
  have hmoment : injectiveMoment H node2235 = injectiveMoment H pivotMatrix2235 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2235 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2235 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2235 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2235 (0 : Fin 4) = raw4814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2235 raw4814; decide +kernel
    rw [heq]
    exact (canonical4814 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2235 (1 : Fin 4)) =
      Sparse.eval value928 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2235 (1 : Fin 4) = raw4596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2235 raw4596; decide +kernel
    rw [heq]
    exact (canonical4596 hH).trans (sound928 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2235 (2 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2235 (2 : Fin 4) = raw4584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2235 raw4584; decide +kernel
    rw [heq]
    exact (canonical4584 hH).trans (sound844 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2235 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2235 (3 : Fin 4) = raw4580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2235 raw4580; decide +kernel
    rw [heq]
    exact (canonical4580 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2235 + (injectiveMoment H (mergeFirst pivotMatrix2235 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2235 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2235 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2235 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2235, value1010, value1314, value844, value928, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2236 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2236 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

theorem sound2236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2236 = Sparse.eval value2236 (momentVector H) := by
  have heq : pivotMatrix2236 = (fun u v => node2236 (pivotPermutation2236 u) v) := by apply Matrix.ext; unfold pivotMatrix2236 node2236 pivotPermutation2236; decide +kernel
  have hmoment : injectiveMoment H node2236 = injectiveMoment H pivotMatrix2236 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2236 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2236 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2236 (0 : Fin 4)) =
      Sparse.eval value831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2236 (0 : Fin 4) = raw4816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2236 raw4816; decide +kernel
    rw [heq]
    exact (canonical4816 hH).trans (sound831 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2236 (1 : Fin 4)) =
      Sparse.eval value729 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2236 (1 : Fin 4) = raw4599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2236 raw4599; decide +kernel
    rw [heq]
    exact (canonical4599 hH).trans (sound729 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2236 (2 : Fin 4)) =
      Sparse.eval value410 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2236 (2 : Fin 4) = raw4585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2236 raw4585; decide +kernel
    rw [heq]
    exact (canonical4585 hH).trans (sound410 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2236 (3 : Fin 4)) =
      Sparse.eval value844 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2236 (3 : Fin 4) = raw4584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2236 raw4584; decide +kernel
    rw [heq]
    exact (canonical4584 hH).trans (sound844 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2236 + (injectiveMoment H (mergeFirst pivotMatrix2236 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2236 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2236 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2236 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2236, value410, value729, value831, value844, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2237 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2237 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound2237 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2237 = Sparse.eval value2237 (momentVector H) := by
  have heq : pivotMatrix2237 = (fun u v => node2237 (pivotPermutation2237 u) v) := by apply Matrix.ext; unfold pivotMatrix2237 node2237 pivotPermutation2237; decide +kernel
  have hmoment : injectiveMoment H node2237 = injectiveMoment H pivotMatrix2237 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2237 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2237 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2237 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2237 (0 : Fin 4) = raw4838 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2237 raw4838; decide +kernel
    rw [heq]
    exact (canonical4838 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2237 (1 : Fin 4)) =
      Sparse.eval value1263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2237 (1 : Fin 4) = raw4618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2237 raw4618; decide +kernel
    rw [heq]
    exact (canonical4618 hH).trans (sound1263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2237 (2 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2237 (2 : Fin 4) = raw4611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2237 raw4611; decide +kernel
    rw [heq]
    exact (canonical4611 hH).trans (sound685 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2237 (3 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2237 (3 : Fin 4) = raw4610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2237 raw4610; decide +kernel
    rw [heq]
    exact (canonical4610 hH).trans (sound1308 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2237 + (injectiveMoment H (mergeFirst pivotMatrix2237 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2237 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2237 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2237 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2237, value1263, value1308, value1309, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2238 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2238 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem sound2238 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2238 = Sparse.eval value2238 (momentVector H) := by
  have heq : pivotMatrix2238 = (fun u v => node2238 (pivotPermutation2238 u) v) := by apply Matrix.ext; unfold pivotMatrix2238 node2238 pivotPermutation2238; decide +kernel
  have hmoment : injectiveMoment H node2238 = injectiveMoment H pivotMatrix2238 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2238 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2238 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2238 (0 : Fin 4)) =
      Sparse.eval value614 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2238 (0 : Fin 4) = raw4839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2238 raw4839; decide +kernel
    rw [heq]
    exact (canonical4839 hH).trans (sound614 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2238 (1 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2238 (1 : Fin 4) = raw4619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2238 raw4619; decide +kernel
    rw [heq]
    exact (canonical4619 hH).trans (sound1360 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2238 (2 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2238 (2 : Fin 4) = raw4612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2238 raw4612; decide +kernel
    rw [heq]
    exact (canonical4612 hH).trans (sound685 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2238 (3 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2238 (3 : Fin 4) = raw4611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2238 raw4611; decide +kernel
    rw [heq]
    exact (canonical4611 hH).trans (sound685 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2238 + (injectiveMoment H (mergeFirst pivotMatrix2238 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2238 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2238 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2238 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2238, value1360, value614, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2239 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2239 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

theorem sound2239 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2239 = Sparse.eval value2239 (momentVector H) := by
  have heq : pivotMatrix2239 = (fun u v => node2239 (pivotPermutation2239 u) v) := by apply Matrix.ext; unfold pivotMatrix2239 node2239 pivotPermutation2239; decide +kernel
  have hmoment : injectiveMoment H node2239 = injectiveMoment H pivotMatrix2239 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2239 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2239 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2239 (0 : Fin 4)) =
      Sparse.eval value620 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2239 (0 : Fin 4) = raw4844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2239 raw4844; decide +kernel
    rw [heq]
    exact (canonical4844 hH).trans (sound620 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2239 (1 : Fin 4)) =
      Sparse.eval value617 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2239 (1 : Fin 4) = raw4626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2239 raw4626; decide +kernel
    rw [heq]
    exact (canonical4626 hH).trans (sound617 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2239 (2 : Fin 4)) =
      Sparse.eval value686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2239 (2 : Fin 4) = raw4623 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2239 raw4623; decide +kernel
    rw [heq]
    exact (canonical4623 hH).trans (sound686 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2239 (3 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2239 (3 : Fin 4) = raw4622 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2239 raw4622; decide +kernel
    rw [heq]
    exact (canonical4622 hH).trans (sound1058 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2239 + (injectiveMoment H (mergeFirst pivotMatrix2239 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2239 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2239 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2239 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2239, value1058, value617, value620, value686, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
