import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical132
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical248
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical262
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical275

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1088 = Sparse.eval value1088 (momentVector H) := by
  have hc : momentVector H 28 = injectiveMoment H node1088 := rfl
  simp [value1088, Sparse.eval, hc]

def pivotPermutation1089 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![1, -1, 2, -2], ![1, 3, -4, 0]]

theorem sound1089 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1089 = Sparse.eval value1089 (momentVector H) := by
  have heq : pivotMatrix1089 = (fun u v => node1089.transpose (pivotPermutation1089 u) v) := by apply Matrix.ext; unfold pivotMatrix1089 node1089 pivotPermutation1089; decide +kernel
  have hmoment : injectiveMoment H node1089 = injectiveMoment H pivotMatrix1089 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1089 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1089 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1089 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1089 (0 : Fin 3) = raw1330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1089 raw1330; decide +kernel
    rw [heq]
    exact (canonical1330 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1089 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1089 (1 : Fin 3) = raw5821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1089 raw5821; decide +kernel
    rw [heq]
    exact (canonical5821 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1089 (2 : Fin 3)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1089 (2 : Fin 3) = raw5845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1089 raw5845; decide +kernel
    rw [heq]
    exact (canonical5845 hH).trans (sound132 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1089 + (injectiveMoment H (mergeFirst pivotMatrix1089 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1089 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1089 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1089, value132, value135, value149, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1090 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![1, 0, 2, -3], ![1, 2, -4, 1]]

theorem sound1090 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1090 = Sparse.eval value1090 (momentVector H) := by
  have heq : pivotMatrix1090 = (fun u v => node1090.transpose (pivotPermutation1090 u) v) := by apply Matrix.ext; unfold pivotMatrix1090 node1090 pivotPermutation1090; decide +kernel
  have hmoment : injectiveMoment H node1090 = injectiveMoment H pivotMatrix1090 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1090 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1090 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1090 (0 : Fin 3)) =
      Sparse.eval value112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1090 (0 : Fin 3) = raw1331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1090 raw1331; decide +kernel
    rw [heq]
    exact (canonical1331 hH).trans (sound112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1090 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1090 (1 : Fin 3) = raw5835 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1090 raw5835; decide +kernel
    rw [heq]
    exact (canonical5835 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1090 (2 : Fin 3)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1090 (2 : Fin 3) = raw5847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1090 raw5847; decide +kernel
    rw [heq]
    exact (canonical5847 hH).trans (sound102 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1090 + (injectiveMoment H (mergeFirst pivotMatrix1090 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1090 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1090 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1090, value102, value112, value146, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1091 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -3, 1, 1], ![1, 4, -3, -2]]

theorem sound1091 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1091 = Sparse.eval value1091 (momentVector H) := by
  have heq : pivotMatrix1091 = (fun u v => node1091.transpose (pivotPermutation1091 u) v) := by apply Matrix.ext; unfold pivotMatrix1091 node1091 pivotPermutation1091; decide +kernel
  have hmoment : injectiveMoment H node1091 = injectiveMoment H pivotMatrix1091 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1091 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1091 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1091 (0 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1091 (0 : Fin 3) = raw2641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1091 raw2641; decide +kernel
    rw [heq]
    exact (canonical2641 hH).trans (sound89 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1091 (1 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1091 (1 : Fin 3) = raw6913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1091 raw6913; decide +kernel
    rw [heq]
    exact (canonical6913 hH).trans (sound166 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1091 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1091 (2 : Fin 3) = raw6942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1091 raw6942; decide +kernel
    rw [heq]
    exact (canonical6942 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1091 + (injectiveMoment H (mergeFirst pivotMatrix1091 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1091 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1091 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1091, value166, value173, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1092 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, -2, 2, -1], ![1, 3, -3, -1]]

theorem sound1092 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1092 = Sparse.eval value1092 (momentVector H) := by
  have heq : pivotMatrix1092 = (fun u v => node1092.transpose (pivotPermutation1092 u) v) := by apply Matrix.ext; unfold pivotMatrix1092 node1092 pivotPermutation1092; decide +kernel
  have hmoment : injectiveMoment H node1092 = injectiveMoment H pivotMatrix1092 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1092 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1092 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1092 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1092 (0 : Fin 3) = raw2508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1092 raw2508; decide +kernel
    rw [heq]
    exact (canonical2508 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1092 (1 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1092 (1 : Fin 3) = raw6596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1092 raw6596; decide +kernel
    rw [heq]
    exact (canonical6596 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1092 (2 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1092 (2 : Fin 3) = raw6713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1092 raw6713; decide +kernel
    rw [heq]
    exact (canonical6713 hH).trans (sound259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1092 + (injectiveMoment H (mergeFirst pivotMatrix1092 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1092 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1092 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1092, value159, value168, value259, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1093 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -2, -1, 2], ![1, 3, -1, -3]]

theorem sound1093 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1093 = Sparse.eval value1093 (momentVector H) := by
  have heq : pivotMatrix1093 = (fun u v => node1093.transpose (pivotPermutation1093 u) v) := by apply Matrix.ext; unfold pivotMatrix1093 node1093 pivotPermutation1093; decide +kernel
  have hmoment : injectiveMoment H node1093 = injectiveMoment H pivotMatrix1093 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1093 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1093 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1093 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1093 (0 : Fin 3) = raw2642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1093 raw2642; decide +kernel
    rw [heq]
    exact (canonical2642 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1093 (1 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1093 (1 : Fin 3) = raw6914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1093 raw6914; decide +kernel
    rw [heq]
    exact (canonical6914 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1093 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1093 (2 : Fin 3) = raw6943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1093 raw6943; decide +kernel
    rw [heq]
    exact (canonical6943 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1093 + (injectiveMoment H (mergeFirst pivotMatrix1093 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1093 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1093 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1093, value159, value222, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1094 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1094 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3]]

theorem sound1094 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1094 = Sparse.eval value1094 (momentVector H) := by
  have heq : pivotMatrix1094 = (fun u v => node1094 (pivotPermutation1094 u) v) := by apply Matrix.ext; unfold pivotMatrix1094 node1094 pivotPermutation1094; decide +kernel
  have hmoment : injectiveMoment H node1094 = injectiveMoment H pivotMatrix1094 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1094 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1094 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1094 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1094 (0 : Fin 3) = raw8822 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1094 raw8822; decide +kernel
    rw [heq]
    exact (canonical8822 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1094 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1094 (1 : Fin 3) = raw6715 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1094 raw6715; decide +kernel
    rw [heq]
    exact (canonical6715 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1094 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1094 (2 : Fin 3) = raw6602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1094 raw6602; decide +kernel
    rw [heq]
    exact (canonical6602 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1094 + (injectiveMoment H (mergeFirst pivotMatrix1094 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1094 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1094 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1094, value246, value261, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1095 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1095 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4]]

theorem sound1095 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1095 = Sparse.eval value1095 (momentVector H) := by
  have heq : pivotMatrix1095 = (fun u v => node1095 (pivotPermutation1095 u) v) := by apply Matrix.ext; unfold pivotMatrix1095 node1095 pivotPermutation1095; decide +kernel
  have hmoment : injectiveMoment H node1095 = injectiveMoment H pivotMatrix1095 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1095 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1095 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1095 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1095 (0 : Fin 3) = raw8378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1095 raw8378; decide +kernel
    rw [heq]
    exact (canonical8378 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1095 (1 : Fin 3)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1095 (1 : Fin 3) = raw6714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1095 raw6714; decide +kernel
    rw [heq]
    exact (canonical6714 hH).trans (sound247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1095 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1095 (2 : Fin 3) = raw6602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1095 raw6602; decide +kernel
    rw [heq]
    exact (canonical6602 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1095 + (injectiveMoment H (mergeFirst pivotMatrix1095 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1095 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1095 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1095, value246, value247, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1096 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

theorem sound1096 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1096 = Sparse.eval value1096 (momentVector H) := by
  have heq : pivotMatrix1096 = (fun u v => node1096.transpose (pivotPermutation1096 u) v) := by apply Matrix.ext; unfold pivotMatrix1096 node1096 pivotPermutation1096; decide +kernel
  have hmoment : injectiveMoment H node1096 = injectiveMoment H pivotMatrix1096 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1096 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1096 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1096 (0 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1096 (0 : Fin 3) = raw2513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1096 raw2513; decide +kernel
    rw [heq]
    exact (canonical2513 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1096 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1096 (1 : Fin 3) = raw6626 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1096 raw6626; decide +kernel
    rw [heq]
    exact (canonical6626 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1096 (2 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1096 (2 : Fin 3) = raw6716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1096 raw6716; decide +kernel
    rw [heq]
    exact (canonical6716 hH).trans (sound227 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1096 + (injectiveMoment H (mergeFirst pivotMatrix1096 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1096 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1096 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1096, value227, value276, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1097 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -1, -3, 3], ![1, 2, 1, -4]]

theorem sound1097 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1097 = Sparse.eval value1097 (momentVector H) := by
  have heq : pivotMatrix1097 = (fun u v => node1097.transpose (pivotPermutation1097 u) v) := by apply Matrix.ext; unfold pivotMatrix1097 node1097 pivotPermutation1097; decide +kernel
  have hmoment : injectiveMoment H node1097 = injectiveMoment H pivotMatrix1097 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1097 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1097 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1097 (0 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1097 (0 : Fin 3) = raw2643 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1097 raw2643; decide +kernel
    rw [heq]
    exact (canonical2643 hH).trans (sound161 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1097 (1 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1097 (1 : Fin 3) = raw6917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1097 raw6917; decide +kernel
    rw [heq]
    exact (canonical6917 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1097 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1097 (2 : Fin 3) = raw6944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1097 raw6944; decide +kernel
    rw [heq]
    exact (canonical6944 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1097 + (injectiveMoment H (mergeFirst pivotMatrix1097 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1097 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1097 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1097, value161, value187, value190, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1098 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -1, -2, 2], ![1, 2, 0, -3]]

theorem sound1098 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1098 = Sparse.eval value1098 (momentVector H) := by
  have heq : pivotMatrix1098 = (fun u v => node1098.transpose (pivotPermutation1098 u) v) := by apply Matrix.ext; unfold pivotMatrix1098 node1098 pivotPermutation1098; decide +kernel
  have hmoment : injectiveMoment H node1098 = injectiveMoment H pivotMatrix1098 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1098 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1098 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1098 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1098 (0 : Fin 3) = raw2645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1098 raw2645; decide +kernel
    rw [heq]
    exact (canonical2645 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1098 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1098 (1 : Fin 3) = raw6920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1098 raw6920; decide +kernel
    rw [heq]
    exact (canonical6920 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1098 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1098 (2 : Fin 3) = raw6945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1098 raw6945; decide +kernel
    rw [heq]
    exact (canonical6945 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1098 + (injectiveMoment H (mergeFirst pivotMatrix1098 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1098 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1098 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1098, value111, value203, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1099 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1099 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3]]

theorem sound1099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1099 = Sparse.eval value1099 (momentVector H) := by
  have heq : pivotMatrix1099 = (fun u v => node1099 (pivotPermutation1099 u) v) := by apply Matrix.ext; unfold pivotMatrix1099 node1099 pivotPermutation1099; decide +kernel
  have hmoment : injectiveMoment H node1099 = injectiveMoment H pivotMatrix1099 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1099 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1099 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1099 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1099 (0 : Fin 3) = raw8386 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1099 raw8386; decide +kernel
    rw [heq]
    exact (canonical8386 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1099 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1099 (1 : Fin 3) = raw6715 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1099 raw6715; decide +kernel
    rw [heq]
    exact (canonical6715 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1099 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1099 (2 : Fin 3) = raw6615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1099 raw6615; decide +kernel
    rw [heq]
    exact (canonical6615 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1099 + (injectiveMoment H (mergeFirst pivotMatrix1099 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1099 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1099 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1099, value181, value261, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1100 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![1, -1, 2, -2], ![1, 2, -4, 1]]

theorem sound1100 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1100 = Sparse.eval value1100 (momentVector H) := by
  have heq : pivotMatrix1100 = (fun u v => node1100.transpose (pivotPermutation1100 u) v) := by apply Matrix.ext; unfold pivotMatrix1100 node1100 pivotPermutation1100; decide +kernel
  have hmoment : injectiveMoment H node1100 = injectiveMoment H pivotMatrix1100 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1100 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1100 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1100 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1100 (0 : Fin 3) = raw2647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1100 raw2647; decide +kernel
    rw [heq]
    exact (canonical2647 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1100 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1100 (1 : Fin 3) = raw6923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1100 raw6923; decide +kernel
    rw [heq]
    exact (canonical6923 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1100 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1100 (2 : Fin 3) = raw6946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1100 raw6946; decide +kernel
    rw [heq]
    exact (canonical6946 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1100 + (injectiveMoment H (mergeFirst pivotMatrix1100 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1100 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1100 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1100, value134, value150, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1101 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![1, -3, 3, -1], ![1, 3, -3, -1]]

theorem sound1101 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1101 = Sparse.eval value1101 (momentVector H) := by
  have heq : pivotMatrix1101 = (fun u v => node1101.transpose (pivotPermutation1101 u) v) := by apply Matrix.ext; unfold pivotMatrix1101 node1101 pivotPermutation1101; decide +kernel
  have hmoment : injectiveMoment H node1101 = injectiveMoment H pivotMatrix1101 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1101 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1101 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1101 (0 : Fin 3)) =
      Sparse.eval value220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1101 (0 : Fin 3) = raw3629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1101 raw3629; decide +kernel
    rw [heq]
    exact (canonical3629 hH).trans (sound220 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1101 (1 : Fin 3)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1101 (1 : Fin 3) = raw7276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1101 raw7276; decide +kernel
    rw [heq]
    exact (canonical7276 hH).trans (sound289 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1101 (2 : Fin 3)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1101 (2 : Fin 3) = raw7357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1101 raw7357; decide +kernel
    rw [heq]
    exact (canonical7357 hH).trans (sound289 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1101 + (injectiveMoment H (mergeFirst pivotMatrix1101 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1101 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1101 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1101, value220, value289, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1102 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1102 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, 0, -3, 3], ![1, 0, 3, -4]]

theorem sound1102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1102 = Sparse.eval value1102 (momentVector H) := by
  have heq : pivotMatrix1102 = (fun u v => node1102 (pivotPermutation1102 u) v) := by apply Matrix.ext; unfold pivotMatrix1102 node1102 pivotPermutation1102; decide +kernel
  have hmoment : injectiveMoment H node1102 = injectiveMoment H pivotMatrix1102 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1102 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1102 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1102 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1102 (0 : Fin 3) = raw7329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1102 raw7329; decide +kernel
    rw [heq]
    exact (canonical7329 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1102 (1 : Fin 3)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1102 (1 : Fin 3) = raw6685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1102 raw6685; decide +kernel
    rw [heq]
    exact (canonical6685 hH).trans (sound249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1102 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1102 (2 : Fin 3) = raw6630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1102 raw6630; decide +kernel
    rw [heq]
    exact (canonical6630 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1102 + (injectiveMoment H (mergeFirst pivotMatrix1102 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1102 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1102 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1102, value248, value249, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1103 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1103 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 0, -3, 3], ![1, 0, 2, -3]]

theorem sound1103 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1103 = Sparse.eval value1103 (momentVector H) := by
  have heq : pivotMatrix1103 = (fun u v => node1103 (pivotPermutation1103 u) v) := by apply Matrix.ext; unfold pivotMatrix1103 node1103 pivotPermutation1103; decide +kernel
  have hmoment : injectiveMoment H node1103 = injectiveMoment H pivotMatrix1103 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1103 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1103 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1103 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1103 (0 : Fin 3) = raw7497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1103 raw7497; decide +kernel
    rw [heq]
    exact (canonical7497 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1103 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1103 (1 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1103 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1103 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1103 (2 : Fin 3) = raw6630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1103 raw6630; decide +kernel
    rw [heq]
    exact (canonical6630 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1103 + (injectiveMoment H (mergeFirst pivotMatrix1103 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1103 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1103 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1103, value248, value263, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1104 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![1, -3, 1, 1], ![1, 3, -2, -2]]

theorem sound1104 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1104 = Sparse.eval value1104 (momentVector H) := by
  have heq : pivotMatrix1104 = (fun u v => node1104.transpose (pivotPermutation1104 u) v) := by apply Matrix.ext; unfold pivotMatrix1104 node1104 pivotPermutation1104; decide +kernel
  have hmoment : injectiveMoment H node1104 = injectiveMoment H pivotMatrix1104 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1104 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1104 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1104 (0 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1104 (0 : Fin 3) = raw3855 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1104 raw3855; decide +kernel
    rw [heq]
    exact (canonical3855 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1104 (1 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1104 (1 : Fin 3) = raw7481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1104 raw7481; decide +kernel
    rw [heq]
    exact (canonical7481 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1104 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1104 (2 : Fin 3) = raw7515 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1104 raw7515; decide +kernel
    rw [heq]
    exact (canonical7515 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1104 + (injectiveMoment H (mergeFirst pivotMatrix1104 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1104 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1104 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1104, value223, value280, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1105 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -3, 1, 1], ![1, 3, -3, -1]]

theorem sound1105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1105 = Sparse.eval value1105 (momentVector H) := by
  have heq : pivotMatrix1105 = (fun u v => node1105.transpose (pivotPermutation1105 u) v) := by apply Matrix.ext; unfold pivotMatrix1105 node1105 pivotPermutation1105; decide +kernel
  have hmoment : injectiveMoment H node1105 = injectiveMoment H pivotMatrix1105 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1105 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1105 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1105 (0 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1105 (0 : Fin 3) = raw4205 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1105 raw4205; decide +kernel
    rw [heq]
    exact (canonical4205 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1105 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1105 (1 : Fin 3) = raw7547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1105 raw7547; decide +kernel
    rw [heq]
    exact (canonical7547 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1105 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1105 (2 : Fin 3) = raw7598 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1105 raw7598; decide +kernel
    rw [heq]
    exact (canonical7598 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1105 + (injectiveMoment H (mergeFirst pivotMatrix1105 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1105 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1105 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1105, value170, value187, value188, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1106 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 3, -2], ![1, -3, 1, 1], ![1, 3, -4, 0]]

theorem sound1106 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1106 = Sparse.eval value1106 (momentVector H) := by
  have heq : pivotMatrix1106 = (fun u v => node1106.transpose (pivotPermutation1106 u) v) := by apply Matrix.ext; unfold pivotMatrix1106 node1106 pivotPermutation1106; decide +kernel
  have hmoment : injectiveMoment H node1106 = injectiveMoment H pivotMatrix1106 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1106 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1106 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1106 (0 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1106 (0 : Fin 3) = raw4240 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1106 raw4240; decide +kernel
    rw [heq]
    exact (canonical4240 hH).trans (sound87 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1106 (1 : Fin 3)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1106 (1 : Fin 3) = raw7611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1106 raw7611; decide +kernel
    rw [heq]
    exact (canonical7611 hH).trans (sound88 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1106 (2 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1106 (2 : Fin 3) = raw7618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1106 raw7618; decide +kernel
    rw [heq]
    exact (canonical7618 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1106 + (injectiveMoment H (mergeFirst pivotMatrix1106 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1106 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1106 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1106, value87, value88, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1107 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![1, -2, 2, -1], ![1, 2, -2, -1]]

theorem sound1107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1107 = Sparse.eval value1107 (momentVector H) := by
  have heq : pivotMatrix1107 = (fun u v => node1107.transpose (pivotPermutation1107 u) v) := by apply Matrix.ext; unfold pivotMatrix1107 node1107 pivotPermutation1107; decide +kernel
  have hmoment : injectiveMoment H node1107 = injectiveMoment H pivotMatrix1107 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1107 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1107 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1107 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1107 (0 : Fin 3) = raw3638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1107 raw3638; decide +kernel
    rw [heq]
    exact (canonical3638 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1107 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1107 (1 : Fin 3) = raw7281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1107 raw7281; decide +kernel
    rw [heq]
    exact (canonical7281 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1107 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1107 (2 : Fin 3) = raw7358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1107 raw7358; decide +kernel
    rw [heq]
    exact (canonical7358 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1107 + (injectiveMoment H (mergeFirst pivotMatrix1107 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1107 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1107 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1107, value224, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1108 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![1, -2, -2, 3], ![1, 2, 1, -4]]

theorem sound1108 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1108 = Sparse.eval value1108 (momentVector H) := by
  have heq : pivotMatrix1108 = (fun u v => node1108.transpose (pivotPermutation1108 u) v) := by apply Matrix.ext; unfold pivotMatrix1108 node1108 pivotPermutation1108; decide +kernel
  have hmoment : injectiveMoment H node1108 = injectiveMoment H pivotMatrix1108 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1108 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1108 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1108 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1108 (0 : Fin 3) = raw3856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1108 raw3856; decide +kernel
    rw [heq]
    exact (canonical3856 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1108 (1 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1108 (1 : Fin 3) = raw7482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1108 raw7482; decide +kernel
    rw [heq]
    exact (canonical7482 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1108 (2 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1108 (2 : Fin 3) = raw7516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1108 raw7516; decide +kernel
    rw [heq]
    exact (canonical7516 hH).trans (sound280 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1108 + (injectiveMoment H (mergeFirst pivotMatrix1108 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1108 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1108 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1108, value225, value280, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1109 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1109 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![1, 0, 2, -3]]

theorem sound1109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1109 = Sparse.eval value1109 (momentVector H) := by
  have heq : pivotMatrix1109 = (fun u v => node1109 (pivotPermutation1109 u) v) := by apply Matrix.ext; unfold pivotMatrix1109 node1109 pivotPermutation1109; decide +kernel
  have hmoment : injectiveMoment H node1109 = injectiveMoment H pivotMatrix1109 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1109 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1109 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1109 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1109 (0 : Fin 3) = raw7333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1109 raw7333; decide +kernel
    rw [heq]
    exact (canonical7333 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1109 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1109 (1 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1109 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1109 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1109 (2 : Fin 3) = raw6640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1109 raw6640; decide +kernel
    rw [heq]
    exact (canonical6640 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1109 + (injectiveMoment H (mergeFirst pivotMatrix1109 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1109 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1109 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1109, value176, value263, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1110 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1110 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 0, -2, 2], ![1, 0, 1, -2]]

theorem sound1110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1110 = Sparse.eval value1110 (momentVector H) := by
  have heq : pivotMatrix1110 = (fun u v => node1110 (pivotPermutation1110 u) v) := by apply Matrix.ext; unfold pivotMatrix1110 node1110 pivotPermutation1110; decide +kernel
  have hmoment : injectiveMoment H node1110 = injectiveMoment H pivotMatrix1110 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1110 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1110 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1110 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1110 (0 : Fin 3) = raw7499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1110 raw7499; decide +kernel
    rw [heq]
    exact (canonical7499 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1110 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1110 (1 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1110 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1110 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1110 (2 : Fin 3) = raw6640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1110 raw6640; decide +kernel
    rw [heq]
    exact (canonical6640 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1110 + (injectiveMoment H (mergeFirst pivotMatrix1110 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1110 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1110 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1110, value176, value230, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1111 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, -1, 2], ![1, 2, -1, -2]]

theorem sound1111 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1111 = Sparse.eval value1111 (momentVector H) := by
  have heq : pivotMatrix1111 = (fun u v => node1111.transpose (pivotPermutation1111 u) v) := by apply Matrix.ext; unfold pivotMatrix1111 node1111 pivotPermutation1111; decide +kernel
  have hmoment : injectiveMoment H node1111 = injectiveMoment H pivotMatrix1111 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1111 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1111 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1111 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1111 (0 : Fin 3) = raw4207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1111 raw4207; decide +kernel
    rw [heq]
    exact (canonical4207 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1111 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1111 (1 : Fin 3) = raw7550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1111 raw7550; decide +kernel
    rw [heq]
    exact (canonical7550 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1111 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1111 (2 : Fin 3) = raw7600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1111 raw7600; decide +kernel
    rw [heq]
    exact (canonical7600 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1111 + (injectiveMoment H (mergeFirst pivotMatrix1111 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1111 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1111 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1111, value210, value224, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1112 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, 0, 1], ![1, 2, -2, -1]]

theorem sound1112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1112 = Sparse.eval value1112 (momentVector H) := by
  have heq : pivotMatrix1112 = (fun u v => node1112.transpose (pivotPermutation1112 u) v) := by apply Matrix.ext; unfold pivotMatrix1112 node1112 pivotPermutation1112; decide +kernel
  have hmoment : injectiveMoment H node1112 = injectiveMoment H pivotMatrix1112 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1112 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1112 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1112 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1112 (0 : Fin 3) = raw4208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1112 raw4208; decide +kernel
    rw [heq]
    exact (canonical4208 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1112 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1112 (1 : Fin 3) = raw7554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1112 raw7554; decide +kernel
    rw [heq]
    exact (canonical7554 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1112 (2 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1112 (2 : Fin 3) = raw7601 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1112 raw7601; decide +kernel
    rw [heq]
    exact (canonical7601 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1112 + (injectiveMoment H (mergeFirst pivotMatrix1112 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1112 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1112 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1112, value203, value207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1113 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, -2, 2, -1], ![1, 2, -4, 1]]

theorem sound1113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1113 = Sparse.eval value1113 (momentVector H) := by
  have heq : pivotMatrix1113 = (fun u v => node1113.transpose (pivotPermutation1113 u) v) := by apply Matrix.ext; unfold pivotMatrix1113 node1113 pivotPermutation1113; decide +kernel
  have hmoment : injectiveMoment H node1113 = injectiveMoment H pivotMatrix1113 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1113 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1113 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1113 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1113 (0 : Fin 3) = raw4209 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1113 raw4209; decide +kernel
    rw [heq]
    exact (canonical4209 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1113 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1113 (1 : Fin 3) = raw7556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1113 raw7556; decide +kernel
    rw [heq]
    exact (canonical7556 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1113 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1113 (2 : Fin 3) = raw7602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1113 raw7602; decide +kernel
    rw [heq]
    exact (canonical7602 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1113 + (injectiveMoment H (mergeFirst pivotMatrix1113 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1113 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1113 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1113, value145, value146, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1114 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1114 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem sound1114 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1114 = Sparse.eval value1114 (momentVector H) := by
  have heq : pivotMatrix1114 = (fun u v => node1114 (pivotPermutation1114 u) v) := by apply Matrix.ext; unfold pivotMatrix1114 node1114 pivotPermutation1114; decide +kernel
  have hmoment : injectiveMoment H node1114 = injectiveMoment H pivotMatrix1114 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1114 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1114 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1114 (0 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1114 (0 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1114 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1114 (1 : Fin 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1114 (1 : Fin 3) = raw6666 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1114 raw6666; decide +kernel
    rw [heq]
    exact (canonical6666 hH).trans (sound65 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1114 (2 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1114 (2 : Fin 3) = raw6680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1114 raw6680; decide +kernel
    rw [heq]
    exact (canonical6680 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1114 + (injectiveMoment H (mergeFirst pivotMatrix1114 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1114 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1114 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1114, value287, value65, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1115 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1115 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -3, 2], ![1, 0, 3, -4]]

theorem sound1115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1115 = Sparse.eval value1115 (momentVector H) := by
  have heq : pivotMatrix1115 = (fun u v => node1115 (pivotPermutation1115 u) v) := by apply Matrix.ext; unfold pivotMatrix1115 node1115 pivotPermutation1115; decide +kernel
  have hmoment : injectiveMoment H node1115 = injectiveMoment H pivotMatrix1115 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1115 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1115 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1115 (0 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1115 (0 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1115 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1115 (1 : Fin 3)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1115 (1 : Fin 3) = raw6685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1115 raw6685; decide +kernel
    rw [heq]
    exact (canonical6685 hH).trans (sound249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1115 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1115 (2 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1115 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1115 + (injectiveMoment H (mergeFirst pivotMatrix1115 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1115 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1115 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1115, value155, value249, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1116 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1116 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem sound1116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1116 = Sparse.eval value1116 (momentVector H) := by
  have heq : pivotMatrix1116 = (fun u v => node1116 (pivotPermutation1116 u) v) := by apply Matrix.ext; unfold pivotMatrix1116 node1116 pivotPermutation1116; decide +kernel
  have hmoment : injectiveMoment H node1116 = injectiveMoment H pivotMatrix1116 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1116 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1116 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1116 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1116 (0 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1116 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1116 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1116 (1 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1116 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1116 (2 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1116 (2 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1116 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1116 + (injectiveMoment H (mergeFirst pivotMatrix1116 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1116 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1116 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1116, value185, value230, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1117 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1117 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem sound1117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1117 = Sparse.eval value1117 (momentVector H) := by
  have heq : pivotMatrix1117 = (fun u v => node1117 (pivotPermutation1117 u) v) := by apply Matrix.ext; unfold pivotMatrix1117 node1117 pivotPermutation1117; decide +kernel
  have hmoment : injectiveMoment H node1117 = injectiveMoment H pivotMatrix1117 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1117 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1117 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1117 (0 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1117 (0 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1117 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1117 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1117 (1 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1117 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1117 (2 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1117 (2 : Fin 3) = raw6699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1117 raw6699; decide +kernel
    rw [heq]
    exact (canonical6699 hH).trans (sound293 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1117 + (injectiveMoment H (mergeFirst pivotMatrix1117 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1117 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1117 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1117, value230, value293, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1118 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1118 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound1118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1118 = Sparse.eval value1118 (momentVector H) := by
  have heq : pivotMatrix1118 = (fun u v => node1118 (pivotPermutation1118 u) v) := by apply Matrix.ext; unfold pivotMatrix1118 node1118 pivotPermutation1118; decide +kernel
  have hmoment : injectiveMoment H node1118 = injectiveMoment H pivotMatrix1118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1118 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1118 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1118 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1118 (0 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1118 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1118 (1 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1118 (1 : Fin 3) = raw6699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1118 raw6699; decide +kernel
    rw [heq]
    exact (canonical6699 hH).trans (sound293 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1118 (2 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1118 (2 : Fin 3) = raw6702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1118 raw6702; decide +kernel
    rw [heq]
    exact (canonical6702 hH).trans (sound293 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1118 + (injectiveMoment H (mergeFirst pivotMatrix1118 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1118 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1118 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1118, value293, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1119 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1119 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem sound1119 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1119 = Sparse.eval value1119 (momentVector H) := by
  have heq : pivotMatrix1119 = (fun u v => node1119 (pivotPermutation1119 u) v) := by apply Matrix.ext; unfold pivotMatrix1119 node1119 pivotPermutation1119; decide +kernel
  have hmoment : injectiveMoment H node1119 = injectiveMoment H pivotMatrix1119 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1119 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1119 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1119 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1119 (0 : Fin 3) = raw6558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1119 raw6558; decide +kernel
    rw [heq]
    exact (canonical6558 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1119 (1 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1119 (1 : Fin 3) = raw6706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1119 raw6706; decide +kernel
    rw [heq]
    exact (canonical6706 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1119 (2 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1119 (2 : Fin 3) = raw6707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1119 raw6707; decide +kernel
    rw [heq]
    exact (canonical6707 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1119 + (injectiveMoment H (mergeFirst pivotMatrix1119 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1119 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1119 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1119, value227, value230, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1120 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1120 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![1, -2, -2, 3]]

theorem sound1120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1120 = Sparse.eval value1120 (momentVector H) := by
  have heq : pivotMatrix1120 = (fun u v => node1120.transpose (pivotPermutation1120 u) v) := by apply Matrix.ext; unfold pivotMatrix1120 node1120 pivotPermutation1120; decide +kernel
  have hmoment : injectiveMoment H node1120 = injectiveMoment H pivotMatrix1120 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1120 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1120 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1120 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1120 (0 : Fin 3) = raw4211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1120 raw4211; decide +kernel
    rw [heq]
    exact (canonical4211 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1120 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1120 (1 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1120 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1120 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1120 (2 : Fin 3) = raw7603 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1120 raw7603; decide +kernel
    rw [heq]
    exact (canonical7603 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1120 + (injectiveMoment H (mergeFirst pivotMatrix1120 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1120 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1120 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1120, value169, value198, value201, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1121 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, -4, 2, 1], ![1, 3, -3, -1]]

theorem sound1121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1121 = Sparse.eval value1121 (momentVector H) := by
  have heq : pivotMatrix1121 = (fun u v => node1121.transpose (pivotPermutation1121 u) v) := by apply Matrix.ext; unfold pivotMatrix1121 node1121 pivotPermutation1121; decide +kernel
  have hmoment : injectiveMoment H node1121 = injectiveMoment H pivotMatrix1121 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1121 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1121 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1121 (0 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1121 (0 : Fin 3) = raw5043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1121 raw5043; decide +kernel
    rw [heq]
    exact (canonical5043 hH).trans (sound228 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1121 (1 : Fin 3)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1121 (1 : Fin 3) = raw7918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1121 raw7918; decide +kernel
    rw [heq]
    exact (canonical7918 hH).trans (sound247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1121 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1121 (2 : Fin 3) = raw7940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1121 raw7940; decide +kernel
    rw [heq]
    exact (canonical7940 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1121 + (injectiveMoment H (mergeFirst pivotMatrix1121 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1121 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1121 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1121, value228, value247, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1122 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1122 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 1, -3, 2], ![1, -1, 2, -2]]

theorem sound1122 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1122 = Sparse.eval value1122 (momentVector H) := by
  have heq : pivotMatrix1122 = (fun u v => node1122 (pivotPermutation1122 u) v) := by apply Matrix.ext; unfold pivotMatrix1122 node1122 pivotPermutation1122; decide +kernel
  have hmoment : injectiveMoment H node1122 = injectiveMoment H pivotMatrix1122 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1122 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1122 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1122 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1122 (0 : Fin 3) = raw7505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1122 raw7505; decide +kernel
    rw [heq]
    exact (canonical7505 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1122 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1122 (1 : Fin 3) = raw6705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1122 raw6705; decide +kernel
    rw [heq]
    exact (canonical6705 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1122 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1122 (2 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1122 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1122 + (injectiveMoment H (mergeFirst pivotMatrix1122 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1122 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1122 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1122, value261, value263, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1123 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1123 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![1, 2, -2, -1]]

theorem sound1123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1123 = Sparse.eval value1123 (momentVector H) := by
  have heq : pivotMatrix1123 = (fun u v => node1123.transpose (pivotPermutation1123 u) v) := by apply Matrix.ext; unfold pivotMatrix1123 node1123 pivotPermutation1123; decide +kernel
  have hmoment : injectiveMoment H node1123 = injectiveMoment H pivotMatrix1123 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1123 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1123 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1123 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1123 (0 : Fin 3) = raw5044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1123 raw5044; decide +kernel
    rw [heq]
    exact (canonical5044 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1123 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1123 (1 : Fin 3) = raw7919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1123 raw7919; decide +kernel
    rw [heq]
    exact (canonical7919 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1123 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1123 (2 : Fin 3) = raw7941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1123 raw7941; decide +kernel
    rw [heq]
    exact (canonical7941 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1123 + (injectiveMoment H (mergeFirst pivotMatrix1123 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1123 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1123 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1123, value176, value229, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1124 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1124 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3]]

theorem sound1124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1124 = Sparse.eval value1124 (momentVector H) := by
  have heq : pivotMatrix1124 = (fun u v => node1124 (pivotPermutation1124 u) v) := by apply Matrix.ext; unfold pivotMatrix1124 node1124 pivotPermutation1124; decide +kernel
  have hmoment : injectiveMoment H node1124 = injectiveMoment H pivotMatrix1124 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1124 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1124 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1124 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1124 (0 : Fin 3) = raw8156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1124 raw8156; decide +kernel
    rw [heq]
    exact (canonical8156 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1124 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1124 (1 : Fin 3) = raw6717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1124 raw6717; decide +kernel
    rw [heq]
    exact (canonical6717 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1124 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1124 (2 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1124 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1124 + (injectiveMoment H (mergeFirst pivotMatrix1124 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1124 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1124 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1124, value263, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1125 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![1, -3, 2, 0], ![1, 2, -4, 1]]

theorem sound1125 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1125 = Sparse.eval value1125 (momentVector H) := by
  have heq : pivotMatrix1125 = (fun u v => node1125.transpose (pivotPermutation1125 u) v) := by apply Matrix.ext; unfold pivotMatrix1125 node1125 pivotPermutation1125; decide +kernel
  have hmoment : injectiveMoment H node1125 = injectiveMoment H pivotMatrix1125 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1125 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1125 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1125 (0 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1125 (0 : Fin 3) = raw5071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1125 raw5071; decide +kernel
    rw [heq]
    exact (canonical5071 hH).trans (sound106 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1125 (1 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1125 (1 : Fin 3) = raw7946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1125 raw7946; decide +kernel
    rw [heq]
    exact (canonical7946 hH).trans (sound106 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1125 (2 : Fin 3)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1125 (2 : Fin 3) = raw7954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1125 raw7954; decide +kernel
    rw [heq]
    exact (canonical7954 hH).trans (sound102 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1125 + (injectiveMoment H (mergeFirst pivotMatrix1125 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1125 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1125 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1125, value102, value106, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1126 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1126 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2]]

theorem sound1126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1126 = Sparse.eval value1126 (momentVector H) := by
  have heq : pivotMatrix1126 = (fun u v => node1126 (pivotPermutation1126 u) v) := by apply Matrix.ext; unfold pivotMatrix1126 node1126 pivotPermutation1126; decide +kernel
  have hmoment : injectiveMoment H node1126 = injectiveMoment H pivotMatrix1126 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1126 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1126 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1126 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1126 (0 : Fin 3) = raw8157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1126 raw8157; decide +kernel
    rw [heq]
    exact (canonical8157 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1126 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1126 (1 : Fin 3) = raw6718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1126 raw6718; decide +kernel
    rw [heq]
    exact (canonical6718 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1126 (2 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1126 (2 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1126 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1126 + (injectiveMoment H (mergeFirst pivotMatrix1126 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1126 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1126 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1126, value230, value44, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1127 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1127 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 2, -2], ![1, -2, 2, -1], ![1, 1, -4, 2]]

theorem sound1127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1127 = Sparse.eval value1127 (momentVector H) := by
  have heq : pivotMatrix1127 = (fun u v => node1127.transpose (pivotPermutation1127 u) v) := by apply Matrix.ext; unfold pivotMatrix1127 node1127 pivotPermutation1127; decide +kernel
  have hmoment : injectiveMoment H node1127 = injectiveMoment H pivotMatrix1127 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1127 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1127 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1127 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1127 (0 : Fin 3) = raw5073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1127 raw5073; decide +kernel
    rw [heq]
    exact (canonical5073 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1127 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1127 (1 : Fin 3) = raw7948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1127 raw7948; decide +kernel
    rw [heq]
    exact (canonical7948 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1127 (2 : Fin 3)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1127 (2 : Fin 3) = raw7955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1127 raw7955; decide +kernel
    rw [heq]
    exact (canonical7955 hH).trans (sound132 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1127 + (injectiveMoment H (mergeFirst pivotMatrix1127 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1127 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1127 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1127, value132, value134, value146, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1128 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1128 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 1, 1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

theorem sound1128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1128 = Sparse.eval value1128 (momentVector H) := by
  have heq : pivotMatrix1128 = (fun u v => node1128 (pivotPermutation1128 u) v) := by apply Matrix.ext; unfold pivotMatrix1128 node1128 pivotPermutation1128; decide +kernel
  have hmoment : injectiveMoment H node1128 = injectiveMoment H pivotMatrix1128 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1128 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1128 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1128 (0 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1128 (0 : Fin 3) = raw7508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1128 raw7508; decide +kernel
    rw [heq]
    exact (canonical7508 hH).trans (sound269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1128 (1 : Fin 3)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1128 (1 : Fin 3) = raw6709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1128 raw6709; decide +kernel
    rw [heq]
    exact (canonical6709 hH).trans (sound247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1128 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1128 (2 : Fin 3) = raw6704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1128 raw6704; decide +kernel
    rw [heq]
    exact (canonical6704 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1128 + (injectiveMoment H (mergeFirst pivotMatrix1128 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1128 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1128 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1128, value247, value263, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1129 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 1, 1, -3], ![1, -2, -2, 3]]

theorem sound1129 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1129 = Sparse.eval value1129 (momentVector H) := by
  have heq : pivotMatrix1129 = (fun u v => node1129.transpose (pivotPermutation1129 u) v) := by apply Matrix.ext; unfold pivotMatrix1129 node1129 pivotPermutation1129; decide +kernel
  have hmoment : injectiveMoment H node1129 = injectiveMoment H pivotMatrix1129 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1129 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1129 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1129 (0 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1129 (0 : Fin 3) = raw5052 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1129 raw5052; decide +kernel
    rw [heq]
    exact (canonical5052 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1129 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1129 (1 : Fin 3) = raw7938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1129 raw7938; decide +kernel
    rw [heq]
    exact (canonical7938 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1129 (2 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1129 (2 : Fin 3) = raw7942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1129 raw7942; decide +kernel
    rw [heq]
    exact (canonical7942 hH).trans (sound244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1129 + (injectiveMoment H (mergeFirst pivotMatrix1129 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1129 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1129 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1129, value175, value223, value244, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1130 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1130 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2]]

theorem sound1130 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1130 = Sparse.eval value1130 (momentVector H) := by
  have heq : pivotMatrix1130 = (fun u v => node1130 (pivotPermutation1130 u) v) := by apply Matrix.ext; unfold pivotMatrix1130 node1130 pivotPermutation1130; decide +kernel
  have hmoment : injectiveMoment H node1130 = injectiveMoment H pivotMatrix1130 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1130 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1130 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1130 (0 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1130 (0 : Fin 4) = raw7377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1130 raw7377; decide +kernel
    rw [heq]
    exact (canonical7377 hH).trans (sound283 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1130 (1 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1130 (1 : Fin 4) = raw6742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1130 raw6742; decide +kernel
    rw [heq]
    exact (canonical6742 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1130 (2 : Fin 4)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1130 (2 : Fin 4) = raw6735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1130 raw6735; decide +kernel
    rw [heq]
    exact (canonical6735 hH).trans (sound275 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1130 (3 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1130 (3 : Fin 4) = raw6734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1130 raw6734; decide +kernel
    rw [heq]
    exact (canonical6734 hH).trans (sound175 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1130 + (injectiveMoment H (mergeFirst pivotMatrix1130 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1130 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1130 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1130 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1130, value175, value275, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1131 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

theorem sound1131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1131 = Sparse.eval value1131 (momentVector H) := by
  have heq : pivotMatrix1131 = (fun u v => node1131 (pivotPermutation1131 u) v) := by apply Matrix.ext; unfold pivotMatrix1131 node1131 pivotPermutation1131; decide +kernel
  have hmoment : injectiveMoment H node1131 = injectiveMoment H pivotMatrix1131 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1131 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1131 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1131 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1131 (0 : Fin 4) = raw8160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1131 raw8160; decide +kernel
    rw [heq]
    exact (canonical8160 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1131 (1 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1131 (1 : Fin 4) = raw6783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1131 raw6783; decide +kernel
    rw [heq]
    exact (canonical6783 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1131 (2 : Fin 4)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1131 (2 : Fin 4) = raw6735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1131 raw6735; decide +kernel
    rw [heq]
    exact (canonical6735 hH).trans (sound275 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1131 (3 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1131 (3 : Fin 4) = raw6727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1131 raw6727; decide +kernel
    rw [heq]
    exact (canonical6727 hH).trans (sound202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1131 + (injectiveMoment H (mergeFirst pivotMatrix1131 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1131 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1131 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1131 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1131, value202, value275, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1132 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

theorem sound1132 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1132 = Sparse.eval value1132 (momentVector H) := by
  have heq : pivotMatrix1132 = (fun u v => node1132 (pivotPermutation1132 u) v) := by apply Matrix.ext; unfold pivotMatrix1132 node1132 pivotPermutation1132; decide +kernel
  have hmoment : injectiveMoment H node1132 = injectiveMoment H pivotMatrix1132 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1132 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1132 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1132 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1132 (0 : Fin 4) = raw8161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1132 raw8161; decide +kernel
    rw [heq]
    exact (canonical8161 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1132 (1 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1132 (1 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1132 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1132 (2 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1132 (2 : Fin 4) = raw6736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1132 raw6736; decide +kernel
    rw [heq]
    exact (canonical6736 hH).trans (sound175 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1132 (3 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1132 (3 : Fin 4) = raw6730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1132 raw6730; decide +kernel
    rw [heq]
    exact (canonical6730 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1132 + (injectiveMoment H (mergeFirst pivotMatrix1132 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1132 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1132 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1132 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1132, value175, value223, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1133 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

theorem sound1133 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1133 = Sparse.eval value1133 (momentVector H) := by
  have heq : pivotMatrix1133 = (fun u v => node1133 (pivotPermutation1133 u) v) := by apply Matrix.ext; unfold pivotMatrix1133 node1133 pivotPermutation1133; decide +kernel
  have hmoment : injectiveMoment H node1133 = injectiveMoment H pivotMatrix1133 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1133 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1133 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1133 (0 : Fin 4)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1133 (0 : Fin 4) = raw8532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1133 raw8532; decide +kernel
    rw [heq]
    exact (canonical8532 hH).trans (sound286 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1133 (1 : Fin 4)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1133 (1 : Fin 4) = raw6823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1133 raw6823; decide +kernel
    rw [heq]
    exact (canonical6823 hH).trans (sound286 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1133 (2 : Fin 4)) =
      Sparse.eval value234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1133 (2 : Fin 4) = raw6738 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1133 raw6738; decide +kernel
    rw [heq]
    exact (canonical6738 hH).trans (sound234 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1133 (3 : Fin 4)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1133 (3 : Fin 4) = raw6733 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1133 raw6733; decide +kernel
    rw [heq]
    exact (canonical6733 hH).trans (sound218 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1133 + (injectiveMoment H (mergeFirst pivotMatrix1133 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1133 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1133 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1133 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1133, value218, value234, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1134 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

theorem sound1134 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1134 = Sparse.eval value1134 (momentVector H) := by
  have heq : pivotMatrix1134 = (fun u v => node1134 (pivotPermutation1134 u) v) := by apply Matrix.ext; unfold pivotMatrix1134 node1134 pivotPermutation1134; decide +kernel
  have hmoment : injectiveMoment H node1134 = injectiveMoment H pivotMatrix1134 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1134 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1134 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1134 (0 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1134 (0 : Fin 4) = raw8162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1134 raw8162; decide +kernel
    rw [heq]
    exact (canonical8162 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1134 (1 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1134 (1 : Fin 4) = raw6788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1134 raw6788; decide +kernel
    rw [heq]
    exact (canonical6788 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1134 (2 : Fin 4)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1134 (2 : Fin 4) = raw6737 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1134 raw6737; decide +kernel
    rw [heq]
    exact (canonical6737 hH).trans (sound244 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1134 (3 : Fin 4)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1134 (3 : Fin 4) = raw6733 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1134 raw6733; decide +kernel
    rw [heq]
    exact (canonical6733 hH).trans (sound218 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1134 + (injectiveMoment H (mergeFirst pivotMatrix1134 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1134 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1134 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1134 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1134, value218, value244, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1135 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound1135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1135 = Sparse.eval value1135 (momentVector H) := by
  have heq : pivotMatrix1135 = (fun u v => node1135 (pivotPermutation1135 u) v) := by apply Matrix.ext; unfold pivotMatrix1135 node1135 pivotPermutation1135; decide +kernel
  have hmoment : injectiveMoment H node1135 = injectiveMoment H pivotMatrix1135 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1135 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1135 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1135 (0 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1135 (0 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1135 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1135 (1 : Fin 4)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1135 (1 : Fin 4) = raw6747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1135 raw6747; decide +kernel
    rw [heq]
    exact (canonical6747 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1135 (2 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1135 (2 : Fin 4) = raw6837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1135 raw6837; decide +kernel
    rw [heq]
    exact (canonical6837 hH).trans (sound283 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1135 (3 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1135 (3 : Fin 4) = raw6856 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1135 raw6856; decide +kernel
    rw [heq]
    exact (canonical6856 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1135 + (injectiveMoment H (mergeFirst pivotMatrix1135 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1135 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1135 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1135 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1135, value181, value227, value283, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1136 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem sound1136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1136 = Sparse.eval value1136 (momentVector H) := by
  have heq : pivotMatrix1136 = (fun u v => node1136 (pivotPermutation1136 u) v) := by apply Matrix.ext; unfold pivotMatrix1136 node1136 pivotPermutation1136; decide +kernel
  have hmoment : injectiveMoment H node1136 = injectiveMoment H pivotMatrix1136 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1136 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1136 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1136 (0 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1136 (0 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1136 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1136 (1 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1136 (1 : Fin 4) = raw6754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1136 raw6754; decide +kernel
    rw [heq]
    exact (canonical6754 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1136 (2 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1136 (2 : Fin 4) = raw6861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1136 raw6861; decide +kernel
    rw [heq]
    exact (canonical6861 hH).trans (sound279 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1136 (3 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1136 (3 : Fin 4) = raw6864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1136 raw6864; decide +kernel
    rw [heq]
    exact (canonical6864 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1136 + (injectiveMoment H (mergeFirst pivotMatrix1136 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1136 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1136 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1136 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1136, value184, value276, value279, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1137 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

theorem sound1137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1137 = Sparse.eval value1137 (momentVector H) := by
  have heq : pivotMatrix1137 = (fun u v => node1137 (pivotPermutation1137 u) v) := by apply Matrix.ext; unfold pivotMatrix1137 node1137 pivotPermutation1137; decide +kernel
  have hmoment : injectiveMoment H node1137 = injectiveMoment H pivotMatrix1137 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1137 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1137 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1137 (0 : Fin 4)) =
      Sparse.eval value186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1137 (0 : Fin 4) = raw2846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1137 raw2846; decide +kernel
    rw [heq]
    exact (canonical2846 hH).trans (sound186 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1137 (1 : Fin 4)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1137 (1 : Fin 4) = raw6762 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1137 raw6762; decide +kernel
    rw [heq]
    exact (canonical6762 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1137 (2 : Fin 4)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1137 (2 : Fin 4) = raw6866 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1137 raw6866; decide +kernel
    rw [heq]
    exact (canonical6866 hH).trans (sound277 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1137 (3 : Fin 4)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1137 (3 : Fin 4) = raw6869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1137 raw6869; decide +kernel
    rw [heq]
    exact (canonical6869 hH).trans (sound273 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1137 + (injectiveMoment H (mergeFirst pivotMatrix1137 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1137 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1137 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1137 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1137, value186, value260, value273, value277, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1138 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem sound1138 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1138 = Sparse.eval value1138 (momentVector H) := by
  have heq : pivotMatrix1138 = (fun u v => node1138 (pivotPermutation1138 u) v) := by apply Matrix.ext; unfold pivotMatrix1138 node1138 pivotPermutation1138; decide +kernel
  have hmoment : injectiveMoment H node1138 = injectiveMoment H pivotMatrix1138 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1138 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1138 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1138 (0 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1138 (0 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1138 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1138 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1138 (1 : Fin 4) = raw6763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1138 raw6763; decide +kernel
    rw [heq]
    exact (canonical6763 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1138 (2 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1138 (2 : Fin 4) = raw6867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1138 raw6867; decide +kernel
    rw [heq]
    exact (canonical6867 hH).trans (sound280 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1138 (3 : Fin 4)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1138 (3 : Fin 4) = raw6871 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1138 raw6871; decide +kernel
    rw [heq]
    exact (canonical6871 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1138 + (injectiveMoment H (mergeFirst pivotMatrix1138 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1138 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1138 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1138 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1138, value187, value261, value280, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1139 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem sound1139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1139 = Sparse.eval value1139 (momentVector H) := by
  have heq : pivotMatrix1139 = (fun u v => node1139 (pivotPermutation1139 u) v) := by apply Matrix.ext; unfold pivotMatrix1139 node1139 pivotPermutation1139; decide +kernel
  have hmoment : injectiveMoment H node1139 = injectiveMoment H pivotMatrix1139 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1139 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1139 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1139 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (0 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1139 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (1 : Fin 4) = raw6764 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw6764; decide +kernel
    rw [heq]
    exact (canonical6764 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1139 (2 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (2 : Fin 4) = raw6868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw6868; decide +kernel
    rw [heq]
    exact (canonical6868 hH).trans (sound285 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1139 (3 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1139 (3 : Fin 4) = raw6872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1139 raw6872; decide +kernel
    rw [heq]
    exact (canonical6872 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1139 + (injectiveMoment H (mergeFirst pivotMatrix1139 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1139 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1139 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1139 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1139, value176, value188, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1140 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem sound1140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1140 = Sparse.eval value1140 (momentVector H) := by
  have heq : pivotMatrix1140 = (fun u v => node1140 (pivotPermutation1140 u) v) := by apply Matrix.ext; unfold pivotMatrix1140 node1140 pivotPermutation1140; decide +kernel
  have hmoment : injectiveMoment H node1140 = injectiveMoment H pivotMatrix1140 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1140 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1140 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1140 (0 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1140 (0 : Fin 4) = raw2851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1140 raw2851; decide +kernel
    rw [heq]
    exact (canonical2851 hH).trans (sound190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1140 (1 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1140 (1 : Fin 4) = raw6771 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1140 raw6771; decide +kernel
    rw [heq]
    exact (canonical6771 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1140 (2 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1140 (2 : Fin 4) = raw6874 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1140 raw6874; decide +kernel
    rw [heq]
    exact (canonical6874 hH).trans (sound281 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1140 (3 : Fin 4)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1140 (3 : Fin 4) = raw6876 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1140 raw6876; decide +kernel
    rw [heq]
    exact (canonical6876 hH).trans (sound286 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1140 + (injectiveMoment H (mergeFirst pivotMatrix1140 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1140 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1140 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1140 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1140, value190, value246, value281, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1141 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound1141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1141 = Sparse.eval value1141 (momentVector H) := by
  have heq : pivotMatrix1141 = (fun u v => node1141 (pivotPermutation1141 u) v) := by apply Matrix.ext; unfold pivotMatrix1141 node1141 pivotPermutation1141; decide +kernel
  have hmoment : injectiveMoment H node1141 = injectiveMoment H pivotMatrix1141 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1141 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1141 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1141 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1141 (0 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1141 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1141 (1 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1141 (1 : Fin 4) = raw6754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1141 raw6754; decide +kernel
    rw [heq]
    exact (canonical6754 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1141 (2 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1141 (2 : Fin 4) = raw6837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1141 raw6837; decide +kernel
    rw [heq]
    exact (canonical6837 hH).trans (sound283 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1141 (3 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1141 (3 : Fin 4) = raw6855 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1141 raw6855; decide +kernel
    rw [heq]
    exact (canonical6855 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1141 + (injectiveMoment H (mergeFirst pivotMatrix1141 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1141 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1141 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1141 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1141, value210, value276, value283, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1142 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem sound1142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1142 = Sparse.eval value1142 (momentVector H) := by
  have heq : pivotMatrix1142 = (fun u v => node1142 (pivotPermutation1142 u) v) := by apply Matrix.ext; unfold pivotMatrix1142 node1142 pivotPermutation1142; decide +kernel
  have hmoment : injectiveMoment H node1142 = injectiveMoment H pivotMatrix1142 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1142 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1142 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1142 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1142 (0 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1142 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1142 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1142 (1 : Fin 4) = raw6763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1142 raw6763; decide +kernel
    rw [heq]
    exact (canonical6763 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1142 (2 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1142 (2 : Fin 4) = raw6862 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1142 raw6862; decide +kernel
    rw [heq]
    exact (canonical6862 hH).trans (sound284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1142 (3 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1142 (3 : Fin 4) = raw6864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1142 raw6864; decide +kernel
    rw [heq]
    exact (canonical6864 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1142 + (injectiveMoment H (mergeFirst pivotMatrix1142 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1142 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1142 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1142 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1142, value203, value261, value284, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1143 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1143 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1]]

theorem sound1143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1143 = Sparse.eval value1143 (momentVector H) := by
  have heq : pivotMatrix1143 = (fun u v => node1143 (pivotPermutation1143 u) v) := by apply Matrix.ext; unfold pivotMatrix1143 node1143 pivotPermutation1143; decide +kernel
  have hmoment : injectiveMoment H node1143 = injectiveMoment H pivotMatrix1143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1143 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1143 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1143 (0 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (0 : Fin 4) = raw8546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw8546; decide +kernel
    rw [heq]
    exact (canonical8546 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1143 (1 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (1 : Fin 4) = raw6867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw6867; decide +kernel
    rw [heq]
    exact (canonical6867 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1143 (2 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (2 : Fin 4) = raw6763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw6763; decide +kernel
    rw [heq]
    exact (canonical6763 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1143 (3 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (3 : Fin 4) = raw6759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw6759; decide +kernel
    rw [heq]
    exact (canonical6759 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1143 + (injectiveMoment H (mergeFirst pivotMatrix1143 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1143 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1143 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1143 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1143, value212, value261, value272, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1144 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1144 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1]]

theorem sound1144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1144 = Sparse.eval value1144 (momentVector H) := by
  have heq : pivotMatrix1144 = (fun u v => node1144 (pivotPermutation1144 u) v) := by apply Matrix.ext; unfold pivotMatrix1144 node1144 pivotPermutation1144; decide +kernel
  have hmoment : injectiveMoment H node1144 = injectiveMoment H pivotMatrix1144 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1144 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1144 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1144 (0 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (0 : Fin 4) = raw8547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw8547; decide +kernel
    rw [heq]
    exact (canonical8547 hH).trans (sound255 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1144 (1 : Fin 4)) =
      Sparse.eval value278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (1 : Fin 4) = raw6873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw6873; decide +kernel
    rw [heq]
    exact (canonical6873 hH).trans (sound278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1144 (2 : Fin 4)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (2 : Fin 4) = raw6770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw6770; decide +kernel
    rw [heq]
    exact (canonical6770 hH).trans (sound245 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1144 (3 : Fin 4)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (3 : Fin 4) = raw6766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw6766; decide +kernel
    rw [heq]
    exact (canonical6766 hH).trans (sound213 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1144 + (injectiveMoment H (mergeFirst pivotMatrix1144 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1144 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1144 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1144 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1144, value213, value245, value255, value278, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1145 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1145 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

theorem sound1145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1145 = Sparse.eval value1145 (momentVector H) := by
  have heq : pivotMatrix1145 = (fun u v => node1145 (pivotPermutation1145 u) v) := by apply Matrix.ext; unfold pivotMatrix1145 node1145 pivotPermutation1145; decide +kernel
  have hmoment : injectiveMoment H node1145 = injectiveMoment H pivotMatrix1145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1145 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1145 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1145 (0 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1145 (0 : Fin 4) = raw5915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1145 raw5915; decide +kernel
    rw [heq]
    exact (canonical5915 hH).trans (sound266 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1145 (1 : Fin 4)) =
      Sparse.eval value278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1145 (1 : Fin 4) = raw6772 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1145 raw6772; decide +kernel
    rw [heq]
    exact (canonical6772 hH).trans (sound278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1145 (2 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1145 (2 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1145 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1145 (3 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1145 (3 : Fin 4) = raw6788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1145 raw6788; decide +kernel
    rw [heq]
    exact (canonical6788 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1145 + (injectiveMoment H (mergeFirst pivotMatrix1145 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1145 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1145 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1145 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1145, value266, value278, value280, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1146 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1146 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2]]

theorem sound1146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1146 = Sparse.eval value1146 (momentVector H) := by
  have heq : pivotMatrix1146 = (fun u v => node1146 (pivotPermutation1146 u) v) := by apply Matrix.ext; unfold pivotMatrix1146 node1146 pivotPermutation1146; decide +kernel
  have hmoment : injectiveMoment H node1146 = injectiveMoment H pivotMatrix1146 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1146 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1146 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1146 (0 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1146 (0 : Fin 4) = raw7411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1146 raw7411; decide +kernel
    rw [heq]
    exact (canonical7411 hH).trans (sound284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1146 (1 : Fin 4)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1146 (1 : Fin 4) = raw6814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1146 raw6814; decide +kernel
    rw [heq]
    exact (canonical6814 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1146 (2 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1146 (2 : Fin 4) = raw6783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1146 raw6783; decide +kernel
    rw [heq]
    exact (canonical6783 hH).trans (sound279 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1146 (3 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1146 (3 : Fin 4) = raw6779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1146 raw6779; decide +kernel
    rw [heq]
    exact (canonical6779 hH).trans (sound268 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1146 + (injectiveMoment H (mergeFirst pivotMatrix1146 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1146 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1146 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1146 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1146, value268, value279, value283, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1147 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1147 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem sound1147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1147 = Sparse.eval value1147 (momentVector H) := by
  have heq : pivotMatrix1147 = (fun u v => node1147 (pivotPermutation1147 u) v) := by apply Matrix.ext; unfold pivotMatrix1147 node1147 pivotPermutation1147; decide +kernel
  have hmoment : injectiveMoment H node1147 = injectiveMoment H pivotMatrix1147 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1147 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1147 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1147 (0 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1147 (0 : Fin 4) = raw7412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1147 raw7412; decide +kernel
    rw [heq]
    exact (canonical7412 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1147 (1 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1147 (1 : Fin 4) = raw6818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1147 raw6818; decide +kernel
    rw [heq]
    exact (canonical6818 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1147 (2 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1147 (2 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1147 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1147 (3 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1147 (3 : Fin 4) = raw6783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1147 raw6783; decide +kernel
    rw [heq]
    exact (canonical6783 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1147 + (injectiveMoment H (mergeFirst pivotMatrix1147 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1147 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1147 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1147 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1147, value279, value280, value284, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1148 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1148 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem sound1148 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1148 = Sparse.eval value1148 (momentVector H) := by
  have heq : pivotMatrix1148 = (fun u v => node1148 (pivotPermutation1148 u) v) := by apply Matrix.ext; unfold pivotMatrix1148 node1148 pivotPermutation1148; decide +kernel
  have hmoment : injectiveMoment H node1148 = injectiveMoment H pivotMatrix1148 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1148 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1148 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1148 (0 : Fin 4)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1148 (0 : Fin 4) = raw7414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1148 raw7414; decide +kernel
    rw [heq]
    exact (canonical7414 hH).trans (sound292 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1148 (1 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1148 (1 : Fin 4) = raw6820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1148 raw6820; decide +kernel
    rw [heq]
    exact (canonical6820 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1148 (2 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1148 (2 : Fin 4) = raw6788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1148 raw6788; decide +kernel
    rw [heq]
    exact (canonical6788 hH).trans (sound281 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1148 (3 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1148 (3 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1148 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1148 + (injectiveMoment H (mergeFirst pivotMatrix1148 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1148 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1148 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1148 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1148, value280, value281, value285, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1149 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1149 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem sound1149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1149 = Sparse.eval value1149 (momentVector H) := by
  have heq : pivotMatrix1149 = (fun u v => node1149 (pivotPermutation1149 u) v) := by apply Matrix.ext; unfold pivotMatrix1149 node1149 pivotPermutation1149; decide +kernel
  have hmoment : injectiveMoment H node1149 = injectiveMoment H pivotMatrix1149 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1149 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1149 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1149 (0 : Fin 4)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1149 (0 : Fin 4) = raw5940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1149 raw5940; decide +kernel
    rw [heq]
    exact (canonical5940 hH).trans (sound269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1149 (1 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1149 (1 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1149 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1149 (2 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1149 (2 : Fin 4) = raw6818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1149 raw6818; decide +kernel
    rw [heq]
    exact (canonical6818 hH).trans (sound284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1149 (3 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1149 (3 : Fin 4) = raw6820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1149 raw6820; decide +kernel
    rw [heq]
    exact (canonical6820 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1149 + (injectiveMoment H (mergeFirst pivotMatrix1149 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1149 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1149 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1149 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1149, value269, value280, value284, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1150 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1150 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem sound1150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1150 = Sparse.eval value1150 (momentVector H) := by
  have heq : pivotMatrix1150 = (fun u v => node1150 (pivotPermutation1150 u) v) := by apply Matrix.ext; unfold pivotMatrix1150 node1150 pivotPermutation1150; decide +kernel
  have hmoment : injectiveMoment H node1150 = injectiveMoment H pivotMatrix1150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1150 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1150 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1150 (0 : Fin 4)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1150 (0 : Fin 4) = raw5942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1150 raw5942; decide +kernel
    rw [heq]
    exact (canonical5942 hH).trans (sound270 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1150 (1 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1150 (1 : Fin 4) = raw6788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1150 raw6788; decide +kernel
    rw [heq]
    exact (canonical6788 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1150 (2 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1150 (2 : Fin 4) = raw6820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1150 raw6820; decide +kernel
    rw [heq]
    exact (canonical6820 hH).trans (sound285 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1150 (3 : Fin 4)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1150 (3 : Fin 4) = raw6823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1150 raw6823; decide +kernel
    rw [heq]
    exact (canonical6823 hH).trans (sound286 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1150 + (injectiveMoment H (mergeFirst pivotMatrix1150 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1150 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1150 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1150 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1150, value270, value281, value285, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1151 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1151 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem sound1151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1151 = Sparse.eval value1151 (momentVector H) := by
  have heq : pivotMatrix1151 = (fun u v => node1151 (pivotPermutation1151 u) v) := by apply Matrix.ext; unfold pivotMatrix1151 node1151 pivotPermutation1151; decide +kernel
  have hmoment : injectiveMoment H node1151 = injectiveMoment H pivotMatrix1151 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1151 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1151 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1151 (0 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1151 (0 : Fin 4) = raw5962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1151 raw5962; decide +kernel
    rw [heq]
    exact (canonical5962 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1151 (1 : Fin 4)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1151 (1 : Fin 4) = raw6830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1151 raw6830; decide +kernel
    rw [heq]
    exact (canonical6830 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1151 (2 : Fin 4)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1151 (2 : Fin 4) = raw6839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1151 raw6839; decide +kernel
    rw [heq]
    exact (canonical6839 hH).trans (sound61 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1151 (3 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1151 (3 : Fin 4) = raw6845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1151 raw6845; decide +kernel
    rw [heq]
    exact (canonical6845 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1151 + (injectiveMoment H (mergeFirst pivotMatrix1151 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1151 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1151 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1151 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1151, value271, value287, value61, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
