import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical132
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical278
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical283
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical311
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1152 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1152 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem sound1152 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1152 = Sparse.eval value1152 (momentVector H) := by
  have heq : pivotMatrix1152 = (fun u v => node1152 (pivotPermutation1152 u) v) := by apply Matrix.ext; unfold pivotMatrix1152 node1152 pivotPermutation1152; decide +kernel
  have hmoment : injectiveMoment H node1152 = injectiveMoment H pivotMatrix1152 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1152 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1152 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1152 (0 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1152 (0 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1152 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1152 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1152 (1 : Fin 4) = raw6831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1152 raw6831; decide +kernel
    rw [heq]
    exact (canonical6831 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1152 (2 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1152 (2 : Fin 4) = raw6845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1152 raw6845; decide +kernel
    rw [heq]
    exact (canonical6845 hH).trans (sound287 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1152 (3 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1152 (3 : Fin 4) = raw6852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1152 raw6852; decide +kernel
    rw [heq]
    exact (canonical6852 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1152 + (injectiveMoment H (mergeFirst pivotMatrix1152 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1152 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1152 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1152 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1152, value272, value287, value288, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1153 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1153 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem sound1153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1153 = Sparse.eval value1153 (momentVector H) := by
  have heq : pivotMatrix1153 = (fun u v => node1153 (pivotPermutation1153 u) v) := by apply Matrix.ext; unfold pivotMatrix1153 node1153 pivotPermutation1153; decide +kernel
  have hmoment : injectiveMoment H node1153 = injectiveMoment H pivotMatrix1153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1153 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1153 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1153 (0 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1153 (0 : Fin 4) = raw7449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1153 raw7449; decide +kernel
    rw [heq]
    exact (canonical7449 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1153 (1 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1153 (1 : Fin 4) = raw6863 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1153 raw6863; decide +kernel
    rw [heq]
    exact (canonical6863 hH).trans (sound288 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1153 (2 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1153 (2 : Fin 4) = raw6852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1153 raw6852; decide +kernel
    rw [heq]
    exact (canonical6852 hH).trans (sound288 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1153 (3 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1153 (3 : Fin 4) = raw6845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1153 raw6845; decide +kernel
    rw [heq]
    exact (canonical6845 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1153 + (injectiveMoment H (mergeFirst pivotMatrix1153 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1153 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1153 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1153 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1153, value287, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1154 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![2, -1, 1, -2], ![0, 3, -4, 1]]

theorem sound1154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1154 = Sparse.eval value1154 (momentVector H) := by
  have heq : pivotMatrix1154 = (fun u v => node1154.transpose (pivotPermutation1154 u) v) := by apply Matrix.ext; unfold pivotMatrix1154 node1154 pivotPermutation1154; decide +kernel
  have hmoment : injectiveMoment H node1154 = injectiveMoment H pivotMatrix1154 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1154 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1154 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1154 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1154 (0 : Fin 3) = raw1336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1154 raw1336; decide +kernel
    rw [heq]
    exact (canonical1336 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1154 (1 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1154 (1 : Fin 3) = raw5996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1154 raw5996; decide +kernel
    rw [heq]
    exact (canonical5996 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1154 (2 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1154 (2 : Fin 3) = raw5997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1154 raw5997; decide +kernel
    rw [heq]
    exact (canonical5997 hH).trans (sound84 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1154 + (injectiveMoment H (mergeFirst pivotMatrix1154 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1154 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1154 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1154, value191, value243, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1155 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![2, -3, 0, 1], ![0, 4, -2, -2]]

theorem sound1155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1155 = Sparse.eval value1155 (momentVector H) := by
  have heq : pivotMatrix1155 = (fun u v => node1155.transpose (pivotPermutation1155 u) v) := by apply Matrix.ext; unfold pivotMatrix1155 node1155 pivotPermutation1155; decide +kernel
  have hmoment : injectiveMoment H node1155 = injectiveMoment H pivotMatrix1155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1155 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1155 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1155 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1155 (0 : Fin 3) = raw2649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1155 raw2649; decide +kernel
    rw [heq]
    exact (canonical2649 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1155 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1155 (1 : Fin 3) = raw6941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1155 raw6941; decide +kernel
    rw [heq]
    exact (canonical6941 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1155 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1155 (2 : Fin 3) = raw6947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1155 raw6947; decide +kernel
    rw [heq]
    exact (canonical6947 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1155 + (injectiveMoment H (mergeFirst pivotMatrix1155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1155, value201, value206, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1156 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1156 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3]]

theorem sound1156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1156 = Sparse.eval value1156 (momentVector H) := by
  have heq : pivotMatrix1156 = (fun u v => node1156 (pivotPermutation1156 u) v) := by apply Matrix.ext; unfold pivotMatrix1156 node1156 pivotPermutation1156; decide +kernel
  have hmoment : injectiveMoment H node1156 = injectiveMoment H pivotMatrix1156 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1156 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1156 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1156 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1156 (0 : Fin 3) = raw8914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1156 raw8914; decide +kernel
    rw [heq]
    exact (canonical8914 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1156 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1156 (1 : Fin 3) = raw6944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1156 raw6944; decide +kernel
    rw [heq]
    exact (canonical6944 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1156 (2 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1156 (2 : Fin 3) = raw6917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1156 raw6917; decide +kernel
    rw [heq]
    exact (canonical6917 hH).trans (sound190 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1156 + (injectiveMoment H (mergeFirst pivotMatrix1156 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1156 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1156 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1156, value187, value190, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1157 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 3, -1], ![2, -2, 1, -1], ![0, 3, -4, 1]]

theorem sound1157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1157 = Sparse.eval value1157 (momentVector H) := by
  have heq : pivotMatrix1157 = (fun u v => node1157.transpose (pivotPermutation1157 u) v) := by apply Matrix.ext; unfold pivotMatrix1157 node1157 pivotPermutation1157; decide +kernel
  have hmoment : injectiveMoment H node1157 = injectiveMoment H pivotMatrix1157 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1157 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1157 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1157 (0 : Fin 3)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1157 (0 : Fin 3) = raw2872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1157 raw2872; decide +kernel
    rw [heq]
    exact (canonical2872 hH).trans (sound83 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1157 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1157 (1 : Fin 3) = raw6970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1157 raw6970; decide +kernel
    rw [heq]
    exact (canonical6970 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1157 (2 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1157 (2 : Fin 3) = raw6971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1157 raw6971; decide +kernel
    rw [heq]
    exact (canonical6971 hH).trans (sound89 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1157 + (injectiveMoment H (mergeFirst pivotMatrix1157 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1157 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1157 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1157, value173, value83, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1158 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 3, -2], ![2, -3, 1, 0], ![0, 3, -4, 1]]

theorem sound1158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1158 = Sparse.eval value1158 (momentVector H) := by
  have heq : pivotMatrix1158 = (fun u v => node1158.transpose (pivotPermutation1158 u) v) := by apply Matrix.ext; unfold pivotMatrix1158 node1158 pivotPermutation1158; decide +kernel
  have hmoment : injectiveMoment H node1158 = injectiveMoment H pivotMatrix1158 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1158 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1158 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1158 (0 : Fin 3)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1158 (0 : Fin 3) = raw4241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1158 raw4241; decide +kernel
    rw [heq]
    exact (canonical4241 hH).trans (sound88 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1158 (1 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1158 (1 : Fin 3) = raw7618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1158 raw7618; decide +kernel
    rw [heq]
    exact (canonical7618 hH).trans (sound87 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1158 (2 : Fin 3)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1158 (2 : Fin 3) = raw7620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1158 raw7620; decide +kernel
    rw [heq]
    exact (canonical7620 hH).trans (sound86 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1158 + (injectiveMoment H (mergeFirst pivotMatrix1158 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1158 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1158 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1158, value86, value87, value88, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1159 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 3, -2], ![2, -2, 1, -1], ![0, 2, -4, 2]]

theorem sound1159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1159 = Sparse.eval value1159 (momentVector H) := by
  have heq : pivotMatrix1159 = (fun u v => node1159.transpose (pivotPermutation1159 u) v) := by apply Matrix.ext; unfold pivotMatrix1159 node1159 pivotPermutation1159; decide +kernel
  have hmoment : injectiveMoment H node1159 = injectiveMoment H pivotMatrix1159 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1159 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1159 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1159 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1159 (0 : Fin 3) = raw4242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1159 raw4242; decide +kernel
    rw [heq]
    exact (canonical4242 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1159 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1159 (1 : Fin 3) = raw7619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1159 raw7619; decide +kernel
    rw [heq]
    exact (canonical7619 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1159 (2 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1159 (2 : Fin 3) = raw7621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1159 raw7621; decide +kernel
    rw [heq]
    exact (canonical7621 hH).trans (sound84 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1159 + (injectiveMoment H (mergeFirst pivotMatrix1159 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1159 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1159 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1159, value201, value84, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1160 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-4, 2, 1, 1], ![5, -1, -2, -2]]

theorem sound1160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1160 = Sparse.eval value1160 (momentVector H) := by
  have heq : pivotMatrix1160 = (fun u v => node1160.transpose (pivotPermutation1160 u) v) := by apply Matrix.ext; unfold pivotMatrix1160 node1160 pivotPermutation1160; decide +kernel
  have hmoment : injectiveMoment H node1160 = injectiveMoment H pivotMatrix1160 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1160 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1160 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1160 (0 : Fin 3)) =
      Sparse.eval value234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1160 (0 : Fin 3) = raw6569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1160 raw6569; decide +kernel
    rw [heq]
    exact (canonical6569 hH).trans (sound234 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1160 (1 : Fin 3)) =
      Sparse.eval value282 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1160 (1 : Fin 3) = raw8796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1160 raw8796; decide +kernel
    rw [heq]
    exact (canonical8796 hH).trans (sound282 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1160 (2 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1160 (2 : Fin 3) = raw8797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1160 raw8797; decide +kernel
    rw [heq]
    exact (canonical8797 hH).trans (sound286 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1160 + (injectiveMoment H (mergeFirst pivotMatrix1160 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1160 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1160 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1160, value234, value282, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1161 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-4, 2, 1, 1], ![5, -2, -2, -1]]

theorem sound1161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1161 = Sparse.eval value1161 (momentVector H) := by
  have heq : pivotMatrix1161 = (fun u v => node1161.transpose (pivotPermutation1161 u) v) := by apply Matrix.ext; unfold pivotMatrix1161 node1161 pivotPermutation1161; decide +kernel
  have hmoment : injectiveMoment H node1161 = injectiveMoment H pivotMatrix1161 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1161 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1161 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1161 (0 : Fin 3)) =
      Sparse.eval value238 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1161 (0 : Fin 3) = raw7463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1161 raw7463; decide +kernel
    rw [heq]
    exact (canonical7463 hH).trans (sound238 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1161 (1 : Fin 3)) =
      Sparse.eval value282 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1161 (1 : Fin 3) = raw9735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1161 raw9735; decide +kernel
    rw [heq]
    exact (canonical9735 hH).trans (sound282 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1161 (2 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1161 (2 : Fin 3) = raw9736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1161 raw9736; decide +kernel
    rw [heq]
    exact (canonical9736 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1161 + (injectiveMoment H (mergeFirst pivotMatrix1161 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1161 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1161 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1161, value238, value281, value282, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1162 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 1, 0, 2], ![4, 1, -2, -3]]

theorem sound1162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1162 = Sparse.eval value1162 (momentVector H) := by
  have heq : pivotMatrix1162 = (fun u v => node1162.transpose (pivotPermutation1162 u) v) := by apply Matrix.ext; unfold pivotMatrix1162 node1162 pivotPermutation1162; decide +kernel
  have hmoment : injectiveMoment H node1162 = injectiveMoment H pivotMatrix1162 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1162 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1162 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1162 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1162 (0 : Fin 3) = raw5807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1162 raw5807; decide +kernel
    rw [heq]
    exact (canonical5807 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1162 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1162 (1 : Fin 3) = raw8221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1162 raw8221; decide +kernel
    rw [heq]
    exact (canonical8221 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1162 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1162 (2 : Fin 3) = raw8226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1162 raw8226; decide +kernel
    rw [heq]
    exact (canonical8226 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1162 + (injectiveMoment H (mergeFirst pivotMatrix1162 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1162 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1162 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1162, value193, value198, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1163 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 2, -1, 2], ![4, 0, -1, -3]]

theorem sound1163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1163 = Sparse.eval value1163 (momentVector H) := by
  have heq : pivotMatrix1163 = (fun u v => node1163.transpose (pivotPermutation1163 u) v) := by apply Matrix.ext; unfold pivotMatrix1163 node1163 pivotPermutation1163; decide +kernel
  have hmoment : injectiveMoment H node1163 = injectiveMoment H pivotMatrix1163 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1163 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1163 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1163 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1163 (0 : Fin 3) = raw5808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1163 raw5808; decide +kernel
    rw [heq]
    exact (canonical5808 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1163 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1163 (1 : Fin 3) = raw8222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1163 raw8222; decide +kernel
    rw [heq]
    exact (canonical8222 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1163 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1163 (2 : Fin 3) = raw8227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1163 raw8227; decide +kernel
    rw [heq]
    exact (canonical8227 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1163 + (injectiveMoment H (mergeFirst pivotMatrix1163 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1163 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1163 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1163, value191, value193, value198, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1164 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 2, 0, 1], ![4, 0, -2, -2]]

theorem sound1164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1164 = Sparse.eval value1164 (momentVector H) := by
  have heq : pivotMatrix1164 = (fun u v => node1164.transpose (pivotPermutation1164 u) v) := by apply Matrix.ext; unfold pivotMatrix1164 node1164 pivotPermutation1164; decide +kernel
  have hmoment : injectiveMoment H node1164 = injectiveMoment H pivotMatrix1164 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1164 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1164 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1164 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (0 : Fin 3) = raw5809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw5809; decide +kernel
    rw [heq]
    exact (canonical5809 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1164 (1 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (1 : Fin 3) = raw8223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw8223; decide +kernel
    rw [heq]
    exact (canonical8223 hH).trans (sound199 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1164 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (2 : Fin 3) = raw8228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw8228; decide +kernel
    rw [heq]
    exact (canonical8228 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1164 + (injectiveMoment H (mergeFirst pivotMatrix1164 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1164 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1164 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1164, value199, value204, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1165 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1165 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 1, -3]]

theorem sound1165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1165 = Sparse.eval value1165 (momentVector H) := by
  have heq : pivotMatrix1165 = (fun u v => node1165 (pivotPermutation1165 u) v) := by apply Matrix.ext; unfold pivotMatrix1165 node1165 pivotPermutation1165; decide +kernel
  have hmoment : injectiveMoment H node1165 = injectiveMoment H pivotMatrix1165 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1165 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1165 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1165 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1165 (0 : Fin 3) = raw9068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1165 raw9068; decide +kernel
    rw [heq]
    exact (canonical9068 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1165 (1 : Fin 3)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1165 (1 : Fin 3) = raw7039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1165 raw7039; decide +kernel
    rw [heq]
    exact (canonical7039 hH).trans (sound83 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1165 (2 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1165 (2 : Fin 3) = raw6988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1165 raw6988; decide +kernel
    rw [heq]
    exact (canonical6988 hH).trans (sound171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1165 + (injectiveMoment H (mergeFirst pivotMatrix1165 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1165 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1165 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1165, value171, value37, value83, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1166 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 3, -1, 1], ![4, -1, -1, -2]]

theorem sound1166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1166 = Sparse.eval value1166 (momentVector H) := by
  have heq : pivotMatrix1166 = (fun u v => node1166.transpose (pivotPermutation1166 u) v) := by apply Matrix.ext; unfold pivotMatrix1166 node1166 pivotPermutation1166; decide +kernel
  have hmoment : injectiveMoment H node1166 = injectiveMoment H pivotMatrix1166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1166 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1166 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1166 (0 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1166 (0 : Fin 3) = raw5810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1166 raw5810; decide +kernel
    rw [heq]
    exact (canonical5810 hH).trans (sound161 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1166 (1 : Fin 3)) =
      Sparse.eval value164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1166 (1 : Fin 3) = raw8224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1166 raw8224; decide +kernel
    rw [heq]
    exact (canonical8224 hH).trans (sound164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1166 (2 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1166 (2 : Fin 3) = raw8230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1166 raw8230; decide +kernel
    rw [heq]
    exact (canonical8230 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1166 + (injectiveMoment H (mergeFirst pivotMatrix1166 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1166 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1166 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1166, value161, value164, value170, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1167 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1167 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem sound1167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1167 = Sparse.eval value1167 (momentVector H) := by
  have heq : pivotMatrix1167 = (fun u v => node1167 (pivotPermutation1167 u) v) := by apply Matrix.ext; unfold pivotMatrix1167 node1167 pivotPermutation1167; decide +kernel
  have hmoment : injectiveMoment H node1167 = injectiveMoment H pivotMatrix1167 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1167 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1167 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1167 (0 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1167 (0 : Fin 3) = raw6105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1167 raw6105; decide +kernel
    rw [heq]
    exact (canonical6105 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1167 (1 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1167 (1 : Fin 3) = raw7016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1167 raw7016; decide +kernel
    rw [heq]
    exact (canonical7016 hH).trans (sound51 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1167 (2 : Fin 3)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1167 (2 : Fin 3) = raw7026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1167 raw7026; decide +kernel
    rw [heq]
    exact (canonical7026 hH).trans (sound255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1167 + (injectiveMoment H (mergeFirst pivotMatrix1167 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1167 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1167 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1167, value254, value255, value51, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1168 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1168 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound1168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1168 = Sparse.eval value1168 (momentVector H) := by
  have heq : pivotMatrix1168 = (fun u v => node1168 (pivotPermutation1168 u) v) := by apply Matrix.ext; unfold pivotMatrix1168 node1168 pivotPermutation1168; decide +kernel
  have hmoment : injectiveMoment H node1168 = injectiveMoment H pivotMatrix1168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1168 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1168 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1168 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1168 (0 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1168 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1168 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1168 (1 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1168 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1168 (2 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1168 (2 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1168 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1168 + (injectiveMoment H (mergeFirst pivotMatrix1168 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1168 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1168 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1168, value149, value150, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1169 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1169 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -3, 4], ![0, 2, 0, -2], ![1, -1, 2, -2]]

theorem sound1169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1169 = Sparse.eval value1169 (momentVector H) := by
  have heq : pivotMatrix1169 = (fun u v => node1169 (pivotPermutation1169 u) v) := by apply Matrix.ext; unfold pivotMatrix1169 node1169 pivotPermutation1169; decide +kernel
  have hmoment : injectiveMoment H node1169 = injectiveMoment H pivotMatrix1169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1169 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1169 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1169 (0 : Fin 3) = raw6113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1169 raw6113; decide +kernel
    rw [heq]
    exact (canonical6113 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1169 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1169 (1 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1169 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1169 (2 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1169 (2 : Fin 3) = raw7037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1169 raw7037; decide +kernel
    rw [heq]
    exact (canonical7037 hH).trans (sound147 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1169 + (injectiveMoment H (mergeFirst pivotMatrix1169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1169, value146, value147, value149, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1170 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1170 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

theorem sound1170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1170 = Sparse.eval value1170 (momentVector H) := by
  have heq : pivotMatrix1170 = (fun u v => node1170 (pivotPermutation1170 u) v) := by apply Matrix.ext; unfold pivotMatrix1170 node1170 pivotPermutation1170; decide +kernel
  have hmoment : injectiveMoment H node1170 = injectiveMoment H pivotMatrix1170 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1170 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1170 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1170 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1170 (0 : Fin 3) = raw7775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1170 raw7775; decide +kernel
    rw [heq]
    exact (canonical7775 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1170 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1170 (1 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1170 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1170 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1170 (2 : Fin 3) = raw7001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1170 raw7001; decide +kernel
    rw [heq]
    exact (canonical7001 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1170 + (injectiveMoment H (mergeFirst pivotMatrix1170 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1170 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1170 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1170, value173, value174, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1171 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1171 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2]]

theorem sound1171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1171 = Sparse.eval value1171 (momentVector H) := by
  have heq : pivotMatrix1171 = (fun u v => node1171 (pivotPermutation1171 u) v) := by apply Matrix.ext; unfold pivotMatrix1171 node1171 pivotPermutation1171; decide +kernel
  have hmoment : injectiveMoment H node1171 = injectiveMoment H pivotMatrix1171 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1171 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1171 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1171 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1171 (0 : Fin 3) = raw9070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1171 raw9070; decide +kernel
    rw [heq]
    exact (canonical9070 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1171 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1171 (1 : Fin 3) = raw7041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1171 raw7041; decide +kernel
    rw [heq]
    exact (canonical7041 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1171 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1171 (2 : Fin 3) = raw7001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1171 raw7001; decide +kernel
    rw [heq]
    exact (canonical7001 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1171 + (injectiveMoment H (mergeFirst pivotMatrix1171 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1171 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1171 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1171, value149, value173, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1172 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, -1, 2], ![4, -1, -1, -2]]

theorem sound1172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1172 = Sparse.eval value1172 (momentVector H) := by
  have heq : pivotMatrix1172 = (fun u v => node1172.transpose (pivotPermutation1172 u) v) := by apply Matrix.ext; unfold pivotMatrix1172 node1172 pivotPermutation1172; decide +kernel
  have hmoment : injectiveMoment H node1172 = injectiveMoment H pivotMatrix1172 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1172 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1172 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1172 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1172 (0 : Fin 3) = raw6889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1172 raw6889; decide +kernel
    rw [heq]
    exact (canonical6889 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1172 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1172 (1 : Fin 3) = raw8884 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1172 raw8884; decide +kernel
    rw [heq]
    exact (canonical8884 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1172 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1172 (2 : Fin 3) = raw8887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1172 raw8887; decide +kernel
    rw [heq]
    exact (canonical8887 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1172 + (injectiveMoment H (mergeFirst pivotMatrix1172 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1172 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1172 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1172, value219, value223, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1173 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, 0, 1], ![4, -1, -2, -1]]

theorem sound1173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1173 = Sparse.eval value1173 (momentVector H) := by
  have heq : pivotMatrix1173 = (fun u v => node1173.transpose (pivotPermutation1173 u) v) := by apply Matrix.ext; unfold pivotMatrix1173 node1173 pivotPermutation1173; decide +kernel
  have hmoment : injectiveMoment H node1173 = injectiveMoment H pivotMatrix1173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1173 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1173 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1173 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1173 (0 : Fin 3) = raw6890 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1173 raw6890; decide +kernel
    rw [heq]
    exact (canonical6890 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1173 (1 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1173 (1 : Fin 3) = raw8885 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1173 raw8885; decide +kernel
    rw [heq]
    exact (canonical8885 hH).trans (sound218 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1173 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1173 (2 : Fin 3) = raw8888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1173 raw8888; decide +kernel
    rw [heq]
    exact (canonical8888 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1173 + (injectiveMoment H (mergeFirst pivotMatrix1173 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1173 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1173 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1173, value206, value215, value218, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1174 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1174 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 1, -2]]

theorem sound1174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1174 = Sparse.eval value1174 (momentVector H) := by
  have heq : pivotMatrix1174 = (fun u v => node1174 (pivotPermutation1174 u) v) := by apply Matrix.ext; unfold pivotMatrix1174 node1174 pivotPermutation1174; decide +kernel
  have hmoment : injectiveMoment H node1174 = injectiveMoment H pivotMatrix1174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1174 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1174 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1174 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1174 (0 : Fin 3) = raw9060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1174 raw9060; decide +kernel
    rw [heq]
    exact (canonical9060 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1174 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1174 (1 : Fin 3) = raw7041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1174 raw7041; decide +kernel
    rw [heq]
    exact (canonical7041 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1174 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1174 (2 : Fin 3) = raw7004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1174 raw7004; decide +kernel
    rw [heq]
    exact (canonical7004 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1174 + (injectiveMoment H (mergeFirst pivotMatrix1174 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1174 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1174 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1174, value149, value155, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1175 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1175 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

theorem sound1175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1175 = Sparse.eval value1175 (momentVector H) := by
  have heq : pivotMatrix1175 = (fun u v => node1175 (pivotPermutation1175 u) v) := by apply Matrix.ext; unfold pivotMatrix1175 node1175 pivotPermutation1175; decide +kernel
  have hmoment : injectiveMoment H node1175 = injectiveMoment H pivotMatrix1175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1175 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1175 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1175 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1175 (0 : Fin 3) = raw8279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1175 raw8279; decide +kernel
    rw [heq]
    exact (canonical8279 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1175 (1 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1175 (1 : Fin 3) = raw7040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1175 raw7040; decide +kernel
    rw [heq]
    exact (canonical7040 hH).trans (sound147 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1175 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1175 (2 : Fin 3) = raw7004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1175 raw7004; decide +kernel
    rw [heq]
    exact (canonical7004 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1175 + (injectiveMoment H (mergeFirst pivotMatrix1175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1175, value147, value155, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1176 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1176 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem sound1176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1176 = Sparse.eval value1176 (momentVector H) := by
  have heq : pivotMatrix1176 = (fun u v => node1176 (pivotPermutation1176 u) v) := by apply Matrix.ext; unfold pivotMatrix1176 node1176 pivotPermutation1176; decide +kernel
  have hmoment : injectiveMoment H node1176 = injectiveMoment H pivotMatrix1176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1176 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1176 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1176 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1176 (0 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1176 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1176 (1 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1176 (1 : Fin 3) = raw7035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1176 raw7035; decide +kernel
    rw [heq]
    exact (canonical7035 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1176 (2 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1176 (2 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1176 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1176 + (injectiveMoment H (mergeFirst pivotMatrix1176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1176, value149, value181, value243, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1177 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1177 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem sound1177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1177 = Sparse.eval value1177 (momentVector H) := by
  have heq : pivotMatrix1177 = (fun u v => node1177 (pivotPermutation1177 u) v) := by apply Matrix.ext; unfold pivotMatrix1177 node1177 pivotPermutation1177; decide +kernel
  have hmoment : injectiveMoment H node1177 = injectiveMoment H pivotMatrix1177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1177 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1177 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1177 (0 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1177 (0 : Fin 3) = raw7783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1177 raw7783; decide +kernel
    rw [heq]
    exact (canonical7783 hH).trans (sound168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1177 (1 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1177 (1 : Fin 3) = raw7035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1177 raw7035; decide +kernel
    rw [heq]
    exact (canonical7035 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1177 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1177 (2 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1177 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1177 + (injectiveMoment H (mergeFirst pivotMatrix1177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1177, value168, value243, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1178 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1178 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2]]

theorem sound1178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1178 = Sparse.eval value1178 (momentVector H) := by
  have heq : pivotMatrix1178 = (fun u v => node1178 (pivotPermutation1178 u) v) := by apply Matrix.ext; unfold pivotMatrix1178 node1178 pivotPermutation1178; decide +kernel
  have hmoment : injectiveMoment H node1178 = injectiveMoment H pivotMatrix1178 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1178 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1178 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1178 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (0 : Fin 3) = raw8286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw8286; decide +kernel
    rw [heq]
    exact (canonical8286 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1178 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (1 : Fin 3) = raw7041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw7041; decide +kernel
    rw [heq]
    exact (canonical7041 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1178 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (2 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1178 + (injectiveMoment H (mergeFirst pivotMatrix1178 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1178 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1178 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1178, value149, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1179 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 2, -1, 2], ![4, -2, -1, -1]]

theorem sound1179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1179 = Sparse.eval value1179 (momentVector H) := by
  have heq : pivotMatrix1179 = (fun u v => node1179.transpose (pivotPermutation1179 u) v) := by apply Matrix.ext; unfold pivotMatrix1179 node1179 pivotPermutation1179; decide +kernel
  have hmoment : injectiveMoment H node1179 = injectiveMoment H pivotMatrix1179 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1179 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1179 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1179 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1179 (0 : Fin 3) = raw7518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1179 raw7518; decide +kernel
    rw [heq]
    exact (canonical7518 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1179 (1 : Fin 3)) =
      Sparse.eval value164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1179 (1 : Fin 3) = raw9952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1179 raw9952; decide +kernel
    rw [heq]
    exact (canonical9952 hH).trans (sound164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1179 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1179 (2 : Fin 3) = raw9956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1179 raw9956; decide +kernel
    rw [heq]
    exact (canonical9956 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1179 + (injectiveMoment H (mergeFirst pivotMatrix1179 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1179 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1179 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1179, value164, value198, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1180 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 2, 0, 1], ![4, -2, -2, 0]]

theorem sound1180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1180 = Sparse.eval value1180 (momentVector H) := by
  have heq : pivotMatrix1180 = (fun u v => node1180.transpose (pivotPermutation1180 u) v) := by apply Matrix.ext; unfold pivotMatrix1180 node1180 pivotPermutation1180; decide +kernel
  have hmoment : injectiveMoment H node1180 = injectiveMoment H pivotMatrix1180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1180 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1180 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1180 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (0 : Fin 3) = raw7519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw7519; decide +kernel
    rw [heq]
    exact (canonical7519 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1180 (1 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (1 : Fin 3) = raw9953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw9953; decide +kernel
    rw [heq]
    exact (canonical9953 hH).trans (sound199 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1180 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (2 : Fin 3) = raw9957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw9957; decide +kernel
    rw [heq]
    exact (canonical9957 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1180 + (injectiveMoment H (mergeFirst pivotMatrix1180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1180, value198, value199, value201, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1181 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1181 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem sound1181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1181 = Sparse.eval value1181 (momentVector H) := by
  have heq : pivotMatrix1181 = (fun u v => node1181 (pivotPermutation1181 u) v) := by apply Matrix.ext; unfold pivotMatrix1181 node1181 pivotPermutation1181; decide +kernel
  have hmoment : injectiveMoment H node1181 = injectiveMoment H pivotMatrix1181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1181 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1181 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1181 (0 : Fin 3)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1181 (0 : Fin 3) = raw7784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1181 raw7784; decide +kernel
    rw [heq]
    exact (canonical7784 hH).trans (sound289 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1181 (1 : Fin 3)) =
      Sparse.eval value290 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1181 (1 : Fin 3) = raw7036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1181 raw7036; decide +kernel
    rw [heq]
    exact (canonical7036 hH).trans (sound290 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1181 (2 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1181 (2 : Fin 3) = raw7022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1181 raw7022; decide +kernel
    rw [heq]
    exact (canonical7022 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1181 + (injectiveMoment H (mergeFirst pivotMatrix1181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1181, value289, value290, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1182 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-3, 3, 1, -1], ![4, -3, -2, 1]]

theorem sound1182 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1182 = Sparse.eval value1182 (momentVector H) := by
  have heq : pivotMatrix1182 = (fun u v => node1182.transpose (pivotPermutation1182 u) v) := by apply Matrix.ext; unfold pivotMatrix1182 node1182 pivotPermutation1182; decide +kernel
  have hmoment : injectiveMoment H node1182 = injectiveMoment H pivotMatrix1182 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1182 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1182 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1182 (0 : Fin 3)) =
      Sparse.eval value251 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1182 (0 : Fin 3) = raw7466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1182 raw7466; decide +kernel
    rw [heq]
    exact (canonical7466 hH).trans (sound251 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1182 (1 : Fin 3)) =
      Sparse.eval value278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1182 (1 : Fin 3) = raw9737 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1182 raw9737; decide +kernel
    rw [heq]
    exact (canonical9737 hH).trans (sound278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1182 (2 : Fin 3)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1182 (2 : Fin 3) = raw9741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1182 raw9741; decide +kernel
    rw [heq]
    exact (canonical9741 hH).trans (sound277 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1182 + (injectiveMoment H (mergeFirst pivotMatrix1182 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1182 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1182 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1182, value251, value277, value278, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1183 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 3, -1, 1], ![4, -3, -1, 0]]

theorem sound1183 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1183 = Sparse.eval value1183 (momentVector H) := by
  have heq : pivotMatrix1183 = (fun u v => node1183.transpose (pivotPermutation1183 u) v) := by apply Matrix.ext; unfold pivotMatrix1183 node1183 pivotPermutation1183; decide +kernel
  have hmoment : injectiveMoment H node1183 = injectiveMoment H pivotMatrix1183 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1183 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1183 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1183 (0 : Fin 3)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1183 (0 : Fin 3) = raw7520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1183 raw7520; decide +kernel
    rw [heq]
    exact (canonical7520 hH).trans (sound221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1183 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1183 (1 : Fin 3) = raw9954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1183 raw9954; decide +kernel
    rw [heq]
    exact (canonical9954 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1183 (2 : Fin 3)) =
      Sparse.eval value220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1183 (2 : Fin 3) = raw9958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1183 raw9958; decide +kernel
    rw [heq]
    exact (canonical9958 hH).trans (sound220 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1183 + (injectiveMoment H (mergeFirst pivotMatrix1183 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1183 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1183 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1183, value193, value220, value221, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1184 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-3, 3, 0, 0], ![4, -3, -2, 1]]

theorem sound1184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1184 = Sparse.eval value1184 (momentVector H) := by
  have heq : pivotMatrix1184 = (fun u v => node1184.transpose (pivotPermutation1184 u) v) := by apply Matrix.ext; unfold pivotMatrix1184 node1184 pivotPermutation1184; decide +kernel
  have hmoment : injectiveMoment H node1184 = injectiveMoment H pivotMatrix1184 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1184 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1184 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1184 (0 : Fin 3)) =
      Sparse.eval value195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1184 (0 : Fin 3) = raw7521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1184 raw7521; decide +kernel
    rw [heq]
    exact (canonical7521 hH).trans (sound195 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1184 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1184 (1 : Fin 3) = raw9955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1184 raw9955; decide +kernel
    rw [heq]
    exact (canonical9955 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1184 (2 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1184 (2 : Fin 3) = raw9959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1184 raw9959; decide +kernel
    rw [heq]
    exact (canonical9959 hH).trans (sound192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1184 + (injectiveMoment H (mergeFirst pivotMatrix1184 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1184 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1184 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1184, value192, value193, value195, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1185 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1185 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -3, 4], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem sound1185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1185 = Sparse.eval value1185 (momentVector H) := by
  have heq : pivotMatrix1185 = (fun u v => node1185 (pivotPermutation1185 u) v) := by apply Matrix.ext; unfold pivotMatrix1185 node1185 pivotPermutation1185; decide +kernel
  have hmoment : injectiveMoment H node1185 = injectiveMoment H pivotMatrix1185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1185 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1185 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1185 (0 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1185 (0 : Fin 3) = raw7787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1185 raw7787; decide +kernel
    rw [heq]
    exact (canonical7787 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1185 (1 : Fin 3)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1185 (1 : Fin 3) = raw7038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1185 raw7038; decide +kernel
    rw [heq]
    exact (canonical7038 hH).trans (sound217 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1185 (2 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1185 (2 : Fin 3) = raw7035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1185 raw7035; decide +kernel
    rw [heq]
    exact (canonical7035 hH).trans (sound243 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1185 + (injectiveMoment H (mergeFirst pivotMatrix1185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1185, value217, value222, value243, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1186 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 1, 1], ![4, -2, -2, 0]]

theorem sound1186 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1186 = Sparse.eval value1186 (momentVector H) := by
  have heq : pivotMatrix1186 = (fun u v => node1186.transpose (pivotPermutation1186 u) v) := by apply Matrix.ext; unfold pivotMatrix1186 node1186 pivotPermutation1186; decide +kernel
  have hmoment : injectiveMoment H node1186 = injectiveMoment H pivotMatrix1186 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1186 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1186 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1186 (0 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1186 (0 : Fin 3) = raw7902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1186 raw7902; decide +kernel
    rw [heq]
    exact (canonical7902 hH).trans (sound244 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1186 (1 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1186 (1 : Fin 3) = raw10090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1186 raw10090; decide +kernel
    rw [heq]
    exact (canonical10090 hH).trans (sound218 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1186 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1186 (2 : Fin 3) = raw10093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1186 raw10093; decide +kernel
    rw [heq]
    exact (canonical10093 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1186 + (injectiveMoment H (mergeFirst pivotMatrix1186 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1186 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1186 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1186, value218, value223, value244, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1187 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-3, 1, 2, 0], ![4, -2, -3, 1]]

theorem sound1187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1187 = Sparse.eval value1187 (momentVector H) := by
  have heq : pivotMatrix1187 = (fun u v => node1187.transpose (pivotPermutation1187 u) v) := by apply Matrix.ext; unfold pivotMatrix1187 node1187 pivotPermutation1187; decide +kernel
  have hmoment : injectiveMoment H node1187 = injectiveMoment H pivotMatrix1187 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1187 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1187 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1187 (0 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1187 (0 : Fin 3) = raw7903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1187 raw7903; decide +kernel
    rw [heq]
    exact (canonical7903 hH).trans (sound241 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1187 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1187 (1 : Fin 3) = raw10091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1187 raw10091; decide +kernel
    rw [heq]
    exact (canonical10091 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1187 (2 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1187 (2 : Fin 3) = raw10094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1187 raw10094; decide +kernel
    rw [heq]
    exact (canonical10094 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1187 + (injectiveMoment H (mergeFirst pivotMatrix1187 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1187 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1187 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1187, value196, value219, value241, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1188 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 1, -1, 2], ![3, 1, -1, -3]]

theorem sound1188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1188 = Sparse.eval value1188 (momentVector H) := by
  have heq : pivotMatrix1188 = (fun u v => node1188.transpose (pivotPermutation1188 u) v) := by apply Matrix.ext; unfold pivotMatrix1188 node1188 pivotPermutation1188; decide +kernel
  have hmoment : injectiveMoment H node1188 = injectiveMoment H pivotMatrix1188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1188 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1188 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1188 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1188 (0 : Fin 3) = raw5811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1188 raw5811; decide +kernel
    rw [heq]
    exact (canonical5811 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1188 (1 : Fin 3)) =
      Sparse.eval value220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1188 (1 : Fin 3) = raw8225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1188 raw8225; decide +kernel
    rw [heq]
    exact (canonical8225 hH).trans (sound220 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1188 (2 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1188 (2 : Fin 3) = raw8233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1188 raw8233; decide +kernel
    rw [heq]
    exact (canonical8233 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1188 + (injectiveMoment H (mergeFirst pivotMatrix1188 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1188 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1188 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1188, value159, value220, value224, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1189 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1189 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4]]

theorem sound1189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1189 = Sparse.eval value1189 (momentVector H) := by
  have heq : pivotMatrix1189 = (fun u v => node1189 (pivotPermutation1189 u) v) := by apply Matrix.ext; unfold pivotMatrix1189 node1189 pivotPermutation1189; decide +kernel
  have hmoment : injectiveMoment H node1189 = injectiveMoment H pivotMatrix1189 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1189 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1189 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1189 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1189 (0 : Fin 3) = raw9067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1189 raw9067; decide +kernel
    rw [heq]
    exact (canonical9067 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1189 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1189 (1 : Fin 3) = raw7125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1189 raw7125; decide +kernel
    rw [heq]
    exact (canonical7125 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1189 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1189 (2 : Fin 3) = raw7061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1189 raw7061; decide +kernel
    rw [heq]
    exact (canonical7061 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1189 + (injectiveMoment H (mergeFirst pivotMatrix1189 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1189 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1189 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1189, value201, value206, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1190 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 2, -1, 1], ![3, 0, -1, -2]]

theorem sound1190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1190 = Sparse.eval value1190 (momentVector H) := by
  have heq : pivotMatrix1190 = (fun u v => node1190.transpose (pivotPermutation1190 u) v) := by apply Matrix.ext; unfold pivotMatrix1190 node1190 pivotPermutation1190; decide +kernel
  have hmoment : injectiveMoment H node1190 = injectiveMoment H pivotMatrix1190 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1190 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1190 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1190 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (0 : Fin 3) = raw5813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw5813; decide +kernel
    rw [heq]
    exact (canonical5813 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1190 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (1 : Fin 3) = raw8227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw8227; decide +kernel
    rw [heq]
    exact (canonical8227 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1190 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1190 (2 : Fin 3) = raw8235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1190 raw8235; decide +kernel
    rw [heq]
    exact (canonical8235 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1190 + (injectiveMoment H (mergeFirst pivotMatrix1190 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1190 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1190 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1190, value111, value198, value203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1191 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1191 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 1, -3]]

theorem sound1191 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1191 = Sparse.eval value1191 (momentVector H) := by
  have heq : pivotMatrix1191 = (fun u v => node1191 (pivotPermutation1191 u) v) := by apply Matrix.ext; unfold pivotMatrix1191 node1191 pivotPermutation1191; decide +kernel
  have hmoment : injectiveMoment H node1191 = injectiveMoment H pivotMatrix1191 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1191 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1191 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1191 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1191 (0 : Fin 3) = raw9068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1191 raw9068; decide +kernel
    rw [heq]
    exact (canonical9068 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1191 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1191 (1 : Fin 3) = raw7126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1191 raw7126; decide +kernel
    rw [heq]
    exact (canonical7126 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1191 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1191 (2 : Fin 3) = raw7067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1191 raw7067; decide +kernel
    rw [heq]
    exact (canonical7067 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1191 + (injectiveMoment H (mergeFirst pivotMatrix1191 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1191 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1191 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1191, value204, value215, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1192 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1192 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 2, 2, -2], ![3, 0, -4, 1]]

theorem sound1192 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1192 = Sparse.eval value1192 (momentVector H) := by
  have heq : pivotMatrix1192 = (fun u v => node1192.transpose (pivotPermutation1192 u) v) := by apply Matrix.ext; unfold pivotMatrix1192 node1192 pivotPermutation1192; decide +kernel
  have hmoment : injectiveMoment H node1192 = injectiveMoment H pivotMatrix1192 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1192 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1192 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1192 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1192 (0 : Fin 3) = raw5815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1192 raw5815; decide +kernel
    rw [heq]
    exact (canonical5815 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1192 (1 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1192 (1 : Fin 3) = raw8229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1192 raw8229; decide +kernel
    rw [heq]
    exact (canonical8229 hH).trans (sound147 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1192 (2 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1192 (2 : Fin 3) = raw8237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1192 raw8237; decide +kernel
    rw [heq]
    exact (canonical8237 hH).trans (sound151 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1192 + (injectiveMoment H (mergeFirst pivotMatrix1192 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1192 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1192 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1192, value135, value147, value151, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1193 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1193 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, 0, -2]]

theorem sound1193 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1193 = Sparse.eval value1193 (momentVector H) := by
  have heq : pivotMatrix1193 = (fun u v => node1193 (pivotPermutation1193 u) v) := by apply Matrix.ext; unfold pivotMatrix1193 node1193 pivotPermutation1193; decide +kernel
  have hmoment : injectiveMoment H node1193 = injectiveMoment H pivotMatrix1193 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1193 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1193 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1193 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1193 (0 : Fin 3) = raw9069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1193 raw9069; decide +kernel
    rw [heq]
    exact (canonical9069 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1193 (1 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1193 (1 : Fin 3) = raw7127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1193 raw7127; decide +kernel
    rw [heq]
    exact (canonical7127 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1193 (2 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1193 (2 : Fin 3) = raw7071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1193 raw7071; decide +kernel
    rw [heq]
    exact (canonical7071 hH).trans (sound107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1193 + (injectiveMoment H (mergeFirst pivotMatrix1193 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1193 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1193 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1193, value107, value177, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1194 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 4, 0, -2], ![3, -2, -2, 1]]

theorem sound1194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1194 = Sparse.eval value1194 (momentVector H) := by
  have heq : pivotMatrix1194 = (fun u v => node1194.transpose (pivotPermutation1194 u) v) := by apply Matrix.ext; unfold pivotMatrix1194 node1194 pivotPermutation1194; decide +kernel
  have hmoment : injectiveMoment H node1194 = injectiveMoment H pivotMatrix1194 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1194 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1194 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1194 (0 : Fin 3)) =
      Sparse.eval value136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1194 (0 : Fin 3) = raw5816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1194 raw5816; decide +kernel
    rw [heq]
    exact (canonical5816 hH).trans (sound136 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1194 (1 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1194 (1 : Fin 3) = raw8231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1194 raw8231; decide +kernel
    rw [heq]
    exact (canonical8231 hH).trans (sound147 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1194 (2 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1194 (2 : Fin 3) = raw8238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1194 raw8238; decide +kernel
    rw [heq]
    exact (canonical8238 hH).trans (sound151 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1194 + (injectiveMoment H (mergeFirst pivotMatrix1194 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1194 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1194 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1194, value136, value147, value151, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1195 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, -1, 1, 2], ![3, 2, -2, -3]]

theorem sound1195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1195 = Sparse.eval value1195 (momentVector H) := by
  have heq : pivotMatrix1195 = (fun u v => node1195.transpose (pivotPermutation1195 u) v) := by apply Matrix.ext; unfold pivotMatrix1195 node1195 pivotPermutation1195; decide +kernel
  have hmoment : injectiveMoment H node1195 = injectiveMoment H pivotMatrix1195 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1195 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1195 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1195 (0 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1195 (0 : Fin 3) = raw6572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1195 raw6572; decide +kernel
    rw [heq]
    exact (canonical6572 hH).trans (sound258 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1195 (1 : Fin 3)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1195 (1 : Fin 3) = raw8798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1195 raw8798; decide +kernel
    rw [heq]
    exact (canonical8798 hH).trans (sound277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1195 (2 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1195 (2 : Fin 3) = raw8802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1195 raw8802; decide +kernel
    rw [heq]
    exact (canonical8802 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1195 + (injectiveMoment H (mergeFirst pivotMatrix1195 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1195 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1195 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1195, value258, value277, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1196 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1196 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, -1, 0, 3], ![3, 2, -2, -3]]

theorem sound1196 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1196 = Sparse.eval value1196 (momentVector H) := by
  have heq : pivotMatrix1196 = (fun u v => node1196.transpose (pivotPermutation1196 u) v) := by apply Matrix.ext; unfold pivotMatrix1196 node1196 pivotPermutation1196; decide +kernel
  have hmoment : injectiveMoment H node1196 = injectiveMoment H pivotMatrix1196 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1196 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1196 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1196 (0 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1196 (0 : Fin 3) = raw6893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1196 raw6893; decide +kernel
    rw [heq]
    exact (canonical6893 hH).trans (sound196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1196 (1 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1196 (1 : Fin 3) = raw8886 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1196 raw8886; decide +kernel
    rw [heq]
    exact (canonical8886 hH).trans (sound213 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1196 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1196 (2 : Fin 3) = raw8894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1196 raw8894; decide +kernel
    rw [heq]
    exact (canonical8894 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1196 + (injectiveMoment H (mergeFirst pivotMatrix1196 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1196 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1196 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1196, value196, value212, value213, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1197 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1197 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem sound1197 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1197 = Sparse.eval value1197 (momentVector H) := by
  have heq : pivotMatrix1197 = (fun u v => node1197 (pivotPermutation1197 u) v) := by apply Matrix.ext; unfold pivotMatrix1197 node1197 pivotPermutation1197; decide +kernel
  have hmoment : injectiveMoment H node1197 = injectiveMoment H pivotMatrix1197 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1197 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1197 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1197 (0 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1197 (0 : Fin 3) = raw6105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1197 raw6105; decide +kernel
    rw [heq]
    exact (canonical6105 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1197 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1197 (1 : Fin 3) = raw7090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1197 raw7090; decide +kernel
    rw [heq]
    exact (canonical7090 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1197 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1197 (2 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1197 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1197 + (injectiveMoment H (mergeFirst pivotMatrix1197 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1197 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1197 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1197, value10, value254, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1198 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1198 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound1198 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1198 = Sparse.eval value1198 (momentVector H) := by
  have heq : pivotMatrix1198 = (fun u v => node1198 (pivotPermutation1198 u) v) := by apply Matrix.ext; unfold pivotMatrix1198 node1198 pivotPermutation1198; decide +kernel
  have hmoment : injectiveMoment H node1198 = injectiveMoment H pivotMatrix1198 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1198 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1198 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1198 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1198 (0 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1198 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1198 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1198 (1 : Fin 3) = raw7101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1198 raw7101; decide +kernel
    rw [heq]
    exact (canonical7101 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1198 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1198 (2 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1198 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1198 + (injectiveMoment H (mergeFirst pivotMatrix1198 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1198 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1198 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1198, value150, value181, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1199 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1199 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound1199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1199 = Sparse.eval value1199 (momentVector H) := by
  have heq : pivotMatrix1199 = (fun u v => node1199 (pivotPermutation1199 u) v) := by apply Matrix.ext; unfold pivotMatrix1199 node1199 pivotPermutation1199; decide +kernel
  have hmoment : injectiveMoment H node1199 = injectiveMoment H pivotMatrix1199 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1199 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1199 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1199 (0 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1199 (0 : Fin 3) = raw6111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1199 raw6111; decide +kernel
    rw [heq]
    exact (canonical6111 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1199 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1199 (1 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1199 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1199 (2 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1199 (2 : Fin 3) = raw7120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1199 raw7120; decide +kernel
    rw [heq]
    exact (canonical7120 hH).trans (sound292 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1199 + (injectiveMoment H (mergeFirst pivotMatrix1199 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1199 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1199 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1199, value254, value292, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1200 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1200 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem sound1200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1200 = Sparse.eval value1200 (momentVector H) := by
  have heq : pivotMatrix1200 = (fun u v => node1200 (pivotPermutation1200 u) v) := by apply Matrix.ext; unfold pivotMatrix1200 node1200 pivotPermutation1200; decide +kernel
  have hmoment : injectiveMoment H node1200 = injectiveMoment H pivotMatrix1200 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1200 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1200 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1200 (0 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1200 (0 : Fin 3) = raw6112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1200 raw6112; decide +kernel
    rw [heq]
    exact (canonical6112 hH).trans (sound228 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1200 (1 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1200 (1 : Fin 3) = raw7114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1200 raw7114; decide +kernel
    rw [heq]
    exact (canonical7114 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1200 (2 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1200 (2 : Fin 3) = raw7122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1200 raw7122; decide +kernel
    rw [heq]
    exact (canonical7122 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1200 + (injectiveMoment H (mergeFirst pivotMatrix1200 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1200 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1200 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1200, value209, value228, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1201 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1201 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem sound1201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1201 = Sparse.eval value1201 (momentVector H) := by
  have heq : pivotMatrix1201 = (fun u v => node1201 (pivotPermutation1201 u) v) := by apply Matrix.ext; unfold pivotMatrix1201 node1201 pivotPermutation1201; decide +kernel
  have hmoment : injectiveMoment H node1201 = injectiveMoment H pivotMatrix1201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1201 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1201 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1201 (0 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1201 (0 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1201 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1201 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1201 (1 : Fin 3) = raw7090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1201 raw7090; decide +kernel
    rw [heq]
    exact (canonical7090 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1201 (2 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1201 (2 : Fin 3) = raw7114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1201 raw7114; decide +kernel
    rw [heq]
    exact (canonical7114 hH).trans (sound269 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1201 + (injectiveMoment H (mergeFirst pivotMatrix1201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1201, value10, value269, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1202 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1202 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound1202 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1202 = Sparse.eval value1202 (momentVector H) := by
  have heq : pivotMatrix1202 = (fun u v => node1202 (pivotPermutation1202 u) v) := by apply Matrix.ext; unfold pivotMatrix1202 node1202 pivotPermutation1202; decide +kernel
  have hmoment : injectiveMoment H node1202 = injectiveMoment H pivotMatrix1202 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1202 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1202 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1202 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (0 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1202 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (1 : Fin 3) = raw7101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw7101; decide +kernel
    rw [heq]
    exact (canonical7101 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1202 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (2 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1202 + (injectiveMoment H (mergeFirst pivotMatrix1202 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1202 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1202 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1202, value271, value272, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1203 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1203 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound1203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1203 = Sparse.eval value1203 (momentVector H) := by
  have heq : pivotMatrix1203 = (fun u v => node1203 (pivotPermutation1203 u) v) := by apply Matrix.ext; unfold pivotMatrix1203 node1203 pivotPermutation1203; decide +kernel
  have hmoment : injectiveMoment H node1203 = injectiveMoment H pivotMatrix1203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1203 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1203 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1203 (0 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1203 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1203 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1203 (1 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1203 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1203 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1203 (2 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1203 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1203 + (injectiveMoment H (mergeFirst pivotMatrix1203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1203, value181, value271, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1204 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1204 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -2, 3], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem sound1204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1204 = Sparse.eval value1204 (momentVector H) := by
  have heq : pivotMatrix1204 = (fun u v => node1204 (pivotPermutation1204 u) v) := by apply Matrix.ext; unfold pivotMatrix1204 node1204 pivotPermutation1204; decide +kernel
  have hmoment : injectiveMoment H node1204 = injectiveMoment H pivotMatrix1204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1204 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1204 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1204 (0 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1204 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1204 (1 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1204 (1 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1204 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1204 (2 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1204 (2 : Fin 3) = raw7122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1204 raw7122; decide +kernel
    rw [heq]
    exact (canonical7122 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1204 + (injectiveMoment H (mergeFirst pivotMatrix1204 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1204 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1204 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1204, value209, value229, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1205 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1205 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 2, -2, 2], ![3, -1, 1, -3]]

theorem sound1205 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1205 = Sparse.eval value1205 (momentVector H) := by
  have heq : pivotMatrix1205 = (fun u v => node1205.transpose (pivotPermutation1205 u) v) := by apply Matrix.ext; unfold pivotMatrix1205 node1205 pivotPermutation1205; decide +kernel
  have hmoment : injectiveMoment H node1205 = injectiveMoment H pivotMatrix1205 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1205 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1205 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1205 (0 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1205 (0 : Fin 3) = raw6574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1205 raw6574; decide +kernel
    rw [heq]
    exact (canonical6574 hH).trans (sound260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1205 (1 : Fin 3)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1205 (1 : Fin 3) = raw8799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1205 raw8799; decide +kernel
    rw [heq]
    exact (canonical8799 hH).trans (sound277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1205 (2 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1205 (2 : Fin 3) = raw8804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1205 raw8804; decide +kernel
    rw [heq]
    exact (canonical8804 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1205 + (injectiveMoment H (mergeFirst pivotMatrix1205 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1205 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1205 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1205, value260, value277, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1206 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1206 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

theorem sound1206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1206 = Sparse.eval value1206 (momentVector H) := by
  have heq : pivotMatrix1206 = (fun u v => node1206 (pivotPermutation1206 u) v) := by apply Matrix.ext; unfold pivotMatrix1206 node1206 pivotPermutation1206; decide +kernel
  have hmoment : injectiveMoment H node1206 = injectiveMoment H pivotMatrix1206 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1206 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1206 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1206 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1206 (0 : Fin 3) = raw7775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1206 raw7775; decide +kernel
    rw [heq]
    exact (canonical7775 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1206 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1206 (1 : Fin 3) = raw7101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1206 raw7101; decide +kernel
    rw [heq]
    exact (canonical7101 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1206 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1206 (2 : Fin 3) = raw7085 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1206 raw7085; decide +kernel
    rw [heq]
    exact (canonical7085 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1206 + (injectiveMoment H (mergeFirst pivotMatrix1206 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1206 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1206 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1206, value174, value185, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1207 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1207 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2]]

theorem sound1207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1207 = Sparse.eval value1207 (momentVector H) := by
  have heq : pivotMatrix1207 = (fun u v => node1207 (pivotPermutation1207 u) v) := by apply Matrix.ext; unfold pivotMatrix1207 node1207 pivotPermutation1207; decide +kernel
  have hmoment : injectiveMoment H node1207 = injectiveMoment H pivotMatrix1207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1207 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1207 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1207 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1207 (0 : Fin 3) = raw9070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1207 raw9070; decide +kernel
    rw [heq]
    exact (canonical9070 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1207 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1207 (1 : Fin 3) = raw7129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1207 raw7129; decide +kernel
    rw [heq]
    exact (canonical7129 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1207 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1207 (2 : Fin 3) = raw7085 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1207 raw7085; decide +kernel
    rw [heq]
    exact (canonical7085 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1207 + (injectiveMoment H (mergeFirst pivotMatrix1207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1207, value181, value185, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1208 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1208 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, 2, -1, 1], ![3, -1, -1, -1]]

theorem sound1208 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1208 = Sparse.eval value1208 (momentVector H) := by
  have heq : pivotMatrix1208 = (fun u v => node1208.transpose (pivotPermutation1208 u) v) := by apply Matrix.ext; unfold pivotMatrix1208 node1208 pivotPermutation1208; decide +kernel
  have hmoment : injectiveMoment H node1208 = injectiveMoment H pivotMatrix1208 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1208 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1208 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1208 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1208 (0 : Fin 3) = raw6895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1208 raw6895; decide +kernel
    rw [heq]
    exact (canonical6895 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1208 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1208 (1 : Fin 3) = raw8887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1208 raw8887; decide +kernel
    rw [heq]
    exact (canonical8887 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1208 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1208 (2 : Fin 3) = raw8896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1208 raw8896; decide +kernel
    rw [heq]
    exact (canonical8896 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1208 + (injectiveMoment H (mergeFirst pivotMatrix1208 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1208 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1208 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1208, value210, value223, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1209 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1209 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, 2, 1, -1], ![3, -1, -3, 1]]

theorem sound1209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1209 = Sparse.eval value1209 (momentVector H) := by
  have heq : pivotMatrix1209 = (fun u v => node1209.transpose (pivotPermutation1209 u) v) := by apply Matrix.ext; unfold pivotMatrix1209 node1209 pivotPermutation1209; decide +kernel
  have hmoment : injectiveMoment H node1209 = injectiveMoment H pivotMatrix1209 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1209 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1209 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1209 (0 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1209 (0 : Fin 3) = raw6896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1209 raw6896; decide +kernel
    rw [heq]
    exact (canonical6896 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1209 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1209 (1 : Fin 3) = raw8889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1209 raw8889; decide +kernel
    rw [heq]
    exact (canonical8889 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1209 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1209 (2 : Fin 3) = raw8897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1209 raw8897; decide +kernel
    rw [heq]
    exact (canonical8897 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1209 + (injectiveMoment H (mergeFirst pivotMatrix1209 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1209 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1209 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1209, value180, value184, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1210 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 3, -2, 1], ![3, -2, 1, -2]]

theorem sound1210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1210 = Sparse.eval value1210 (momentVector H) := by
  have heq : pivotMatrix1210 = (fun u v => node1210.transpose (pivotPermutation1210 u) v) := by apply Matrix.ext; unfold pivotMatrix1210 node1210 pivotPermutation1210; decide +kernel
  have hmoment : injectiveMoment H node1210 = injectiveMoment H pivotMatrix1210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1210 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1210 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1210 (0 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1210 (0 : Fin 3) = raw6576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1210 raw6576; decide +kernel
    rw [heq]
    exact (canonical6576 hH).trans (sound262 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1210 (1 : Fin 3)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1210 (1 : Fin 3) = raw8800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1210 raw8800; decide +kernel
    rw [heq]
    exact (canonical8800 hH).trans (sound265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1210 (2 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1210 (2 : Fin 3) = raw8806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1210 raw8806; decide +kernel
    rw [heq]
    exact (canonical8806 hH).trans (sound268 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1210 + (injectiveMoment H (mergeFirst pivotMatrix1210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1210, value262, value265, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1211 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1211 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 0, 0, -1]]

theorem sound1211 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1211 = Sparse.eval value1211 (momentVector H) := by
  have heq : pivotMatrix1211 = (fun u v => node1211 (pivotPermutation1211 u) v) := by apply Matrix.ext; unfold pivotMatrix1211 node1211 pivotPermutation1211; decide +kernel
  have hmoment : injectiveMoment H node1211 = injectiveMoment H pivotMatrix1211 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1211 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1211 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1211 (0 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1211 (0 : Fin 3) = raw7776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1211 raw7776; decide +kernel
    rw [heq]
    exact (canonical7776 hH).trans (sound269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1211 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1211 (1 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1211 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1211 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1211 (2 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1211 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1211 + (injectiveMoment H (mergeFirst pivotMatrix1211 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1211 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1211 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1211, value263, value269, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1212 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1212 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 0, -1, 0]]

theorem sound1212 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1212 = Sparse.eval value1212 (momentVector H) := by
  have heq : pivotMatrix1212 = (fun u v => node1212 (pivotPermutation1212 u) v) := by apply Matrix.ext; unfold pivotMatrix1212 node1212 pivotPermutation1212; decide +kernel
  have hmoment : injectiveMoment H node1212 = injectiveMoment H pivotMatrix1212 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1212 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1212 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1212 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1212 (0 : Fin 3) = raw7815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1212 raw7815; decide +kernel
    rw [heq]
    exact (canonical7815 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1212 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1212 (1 : Fin 3) = raw7108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1212 raw7108; decide +kernel
    rw [heq]
    exact (canonical7108 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1212 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1212 (2 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1212 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1212 + (injectiveMoment H (mergeFirst pivotMatrix1212 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1212 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1212 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1212, value263, value272, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1213 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 3, 1, -2], ![3, -2, -2, 1]]

theorem sound1213 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1213 = Sparse.eval value1213 (momentVector H) := by
  have heq : pivotMatrix1213 = (fun u v => node1213.transpose (pivotPermutation1213 u) v) := by apply Matrix.ext; unfold pivotMatrix1213 node1213 pivotPermutation1213; decide +kernel
  have hmoment : injectiveMoment H node1213 = injectiveMoment H pivotMatrix1213 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1213 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1213 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1213 (0 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1213 (0 : Fin 3) = raw6577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1213 raw6577; decide +kernel
    rw [heq]
    exact (canonical6577 hH).trans (sound262 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1213 (1 : Fin 3)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1213 (1 : Fin 3) = raw8801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1213 raw8801; decide +kernel
    rw [heq]
    exact (canonical8801 hH).trans (sound273 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1213 (2 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1213 (2 : Fin 3) = raw8807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1213 raw8807; decide +kernel
    rw [heq]
    exact (canonical8807 hH).trans (sound274 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1213 + (injectiveMoment H (mergeFirst pivotMatrix1213 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1213 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1213 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1213, value262, value273, value274, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1214 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1214 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

theorem sound1214 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1214 = Sparse.eval value1214 (momentVector H) := by
  have heq : pivotMatrix1214 = (fun u v => node1214 (pivotPermutation1214 u) v) := by apply Matrix.ext; unfold pivotMatrix1214 node1214 pivotPermutation1214; decide +kernel
  have hmoment : injectiveMoment H node1214 = injectiveMoment H pivotMatrix1214 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1214 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1214 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1214 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1214 (0 : Fin 3) = raw8296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1214 raw8296; decide +kernel
    rw [heq]
    exact (canonical8296 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1214 (1 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1214 (1 : Fin 3) = raw7128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1214 raw7128; decide +kernel
    rw [heq]
    exact (canonical7128 hH).trans (sound209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1214 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1214 (2 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1214 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1214 + (injectiveMoment H (mergeFirst pivotMatrix1214 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1214 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1214 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1214, value209, value263, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1215 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-2, 3, 0, -1], ![3, -2, -2, 1]]

theorem sound1215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1215 = Sparse.eval value1215 (momentVector H) := by
  have heq : pivotMatrix1215 = (fun u v => node1215.transpose (pivotPermutation1215 u) v) := by apply Matrix.ext; unfold pivotMatrix1215 node1215 pivotPermutation1215; decide +kernel
  have hmoment : injectiveMoment H node1215 = injectiveMoment H pivotMatrix1215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1215 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1215 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1215 (0 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1215 (0 : Fin 3) = raw6898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1215 raw6898; decide +kernel
    rw [heq]
    exact (canonical6898 hH).trans (sound209 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1215 (1 : Fin 3)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1215 (1 : Fin 3) = raw8890 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1215 raw8890; decide +kernel
    rw [heq]
    exact (canonical8890 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1215 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1215 (2 : Fin 3) = raw8899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1215 raw8899; decide +kernel
    rw [heq]
    exact (canonical8899 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1215 + (injectiveMoment H (mergeFirst pivotMatrix1215 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1215 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1215 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1215, value209, value212, value214, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
