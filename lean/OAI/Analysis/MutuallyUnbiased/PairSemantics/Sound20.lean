import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical248
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical278
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical283
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical287
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical311
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical316
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical317

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1280 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem sound1280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1280 = Sparse.eval value1280 (momentVector H) := by
  have heq : pivotMatrix1280 = (fun u v => node1280 (pivotPermutation1280 u) v) := by apply Matrix.ext; unfold pivotMatrix1280 node1280 pivotPermutation1280; decide +kernel
  have hmoment : injectiveMoment H node1280 = injectiveMoment H pivotMatrix1280 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1280 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1280 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1280 (0 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1280 (0 : Fin 3) = raw6702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1280 raw6702; decide +kernel
    rw [heq]
    exact (canonical6702 hH).trans (sound293 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1280 (1 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1280 (1 : Fin 3) = raw8819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1280 raw8819; decide +kernel
    rw [heq]
    exact (canonical8819 hH).trans (sound64 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1280 (2 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1280 (2 : Fin 3) = raw8879 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1280 raw8879; decide +kernel
    rw [heq]
    exact (canonical8879 hH).trans (sound64 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1280 + (injectiveMoment H (mergeFirst pivotMatrix1280 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1280 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1280 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1280, value293, value64, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1281 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem sound1281 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1281 = Sparse.eval value1281 (momentVector H) := by
  have heq : pivotMatrix1281 = (fun u v => node1281 (pivotPermutation1281 u) v) := by apply Matrix.ext; unfold pivotMatrix1281 node1281 pivotPermutation1281; decide +kernel
  have hmoment : injectiveMoment H node1281 = injectiveMoment H pivotMatrix1281 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1281 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1281 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1281 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1281 (0 : Fin 3) = raw6935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1281 raw6935; decide +kernel
    rw [heq]
    exact (canonical6935 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1281 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1281 (1 : Fin 3) = raw8909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1281 raw8909; decide +kernel
    rw [heq]
    exact (canonical8909 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1281 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1281 (2 : Fin 3) = raw8923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1281 raw8923; decide +kernel
    rw [heq]
    exact (canonical8923 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1281 + (injectiveMoment H (mergeFirst pivotMatrix1281 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1281 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1281 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1281, value203, value210, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1282 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem sound1282 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1282 = Sparse.eval value1282 (momentVector H) := by
  have heq : pivotMatrix1282 = (fun u v => node1282 (pivotPermutation1282 u) v) := by apply Matrix.ext; unfold pivotMatrix1282 node1282 pivotPermutation1282; decide +kernel
  have hmoment : injectiveMoment H node1282 = injectiveMoment H pivotMatrix1282 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1282 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1282 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1282 (0 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1282 (0 : Fin 3) = raw6936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1282 raw6936; decide +kernel
    rw [heq]
    exact (canonical6936 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1282 (1 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1282 (1 : Fin 3) = raw8910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1282 raw8910; decide +kernel
    rw [heq]
    exact (canonical8910 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1282 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1282 (2 : Fin 3) = raw8924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1282 raw8924; decide +kernel
    rw [heq]
    exact (canonical8924 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1282 + (injectiveMoment H (mergeFirst pivotMatrix1282 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1282 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1282 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1282, value180, value187, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1283 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -2, 2]]

theorem sound1283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1283 = Sparse.eval value1283 (momentVector H) := by
  have heq : pivotMatrix1283 = (fun u v => node1283 (pivotPermutation1283 u) v) := by apply Matrix.ext; unfold pivotMatrix1283 node1283 pivotPermutation1283; decide +kernel
  have hmoment : injectiveMoment H node1283 = injectiveMoment H pivotMatrix1283 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1283 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1283 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1283 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1283 (0 : Fin 3) = raw6967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1283 raw6967; decide +kernel
    rw [heq]
    exact (canonical6967 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1283 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1283 (1 : Fin 3) = raw8939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1283 raw8939; decide +kernel
    rw [heq]
    exact (canonical8939 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1283 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1283 (2 : Fin 3) = raw8945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1283 raw8945; decide +kernel
    rw [heq]
    exact (canonical8945 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1283 + (injectiveMoment H (mergeFirst pivotMatrix1283 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1283 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1283 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1283, value226, value229, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1284 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem sound1284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1284 = Sparse.eval value1284 (momentVector H) := by
  have heq : pivotMatrix1284 = (fun u v => node1284 (pivotPermutation1284 u) v) := by apply Matrix.ext; unfold pivotMatrix1284 node1284 pivotPermutation1284; decide +kernel
  have hmoment : injectiveMoment H node1284 = injectiveMoment H pivotMatrix1284 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1284 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1284 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1284 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1284 (0 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1284 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1284 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1284 (1 : Fin 3) = raw9086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1284 raw9086; decide +kernel
    rw [heq]
    exact (canonical9086 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1284 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1284 (2 : Fin 3) = raw9154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1284 raw9154; decide +kernel
    rw [heq]
    exact (canonical9154 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1284 + (injectiveMoment H (mergeFirst pivotMatrix1284 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1284 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1284 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1284, value272, value291, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1285 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

theorem sound1285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1285 = Sparse.eval value1285 (momentVector H) := by
  have heq : pivotMatrix1285 = (fun u v => node1285 (pivotPermutation1285 u) v) := by apply Matrix.ext; unfold pivotMatrix1285 node1285 pivotPermutation1285; decide +kernel
  have hmoment : injectiveMoment H node1285 = injectiveMoment H pivotMatrix1285 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1285 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1285 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1285 (0 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1285 (0 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1285 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1285 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1285 (1 : Fin 3) = raw9978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1285 raw9978; decide +kernel
    rw [heq]
    exact (canonical9978 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1285 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1285 (2 : Fin 3) = raw9984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1285 raw9984; decide +kernel
    rw [heq]
    exact (canonical9984 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1285 + (injectiveMoment H (mergeFirst pivotMatrix1285 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1285 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1285 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1285, value169, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1286 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem sound1286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1286 = Sparse.eval value1286 (momentVector H) := by
  have heq : pivotMatrix1286 = (fun u v => node1286 (pivotPermutation1286 u) v) := by apply Matrix.ext; unfold pivotMatrix1286 node1286 pivotPermutation1286; decide +kernel
  have hmoment : injectiveMoment H node1286 = injectiveMoment H pivotMatrix1286 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1286 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1286 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1286 (0 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1286 (0 : Fin 3) = raw7786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1286 raw7786; decide +kernel
    rw [heq]
    exact (canonical7786 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1286 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1286 (1 : Fin 3) = raw9994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1286 raw9994; decide +kernel
    rw [heq]
    exact (canonical9994 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1286 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1286 (2 : Fin 3) = raw9995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1286 raw9995; decide +kernel
    rw [heq]
    exact (canonical9995 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1286 + (injectiveMoment H (mergeFirst pivotMatrix1286 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1286 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1286 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1286, value180, value261, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1287 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem sound1287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1287 = Sparse.eval value1287 (momentVector H) := by
  have heq : pivotMatrix1287 = (fun u v => node1287 (pivotPermutation1287 u) v) := by apply Matrix.ext; unfold pivotMatrix1287 node1287 pivotPermutation1287; decide +kernel
  have hmoment : injectiveMoment H node1287 = injectiveMoment H pivotMatrix1287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1287 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1287 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1287 (0 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1287 (0 : Fin 4) = raw4144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1287 raw4144; decide +kernel
    rw [heq]
    exact (canonical4144 hH).trans (sound214 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1287 (1 : Fin 4)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1287 (1 : Fin 4) = raw7401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1287 raw7401; decide +kernel
    rw [heq]
    exact (canonical7401 hH).trans (sound259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1287 (2 : Fin 4)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1287 (2 : Fin 4) = raw7458 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1287 raw7458; decide +kernel
    rw [heq]
    exact (canonical7458 hH).trans (sound289 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1287 (3 : Fin 4)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1287 (3 : Fin 4) = raw7460 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1287 raw7460; decide +kernel
    rw [heq]
    exact (canonical7460 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1287 + (injectiveMoment H (mergeFirst pivotMatrix1287 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1287 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1287 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1287 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1287, value214, value259, value289, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1288 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem sound1288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1288 = Sparse.eval value1288 (momentVector H) := by
  have heq : pivotMatrix1288 = (fun u v => node1288 (pivotPermutation1288 u) v) := by apply Matrix.ext; unfold pivotMatrix1288 node1288 pivotPermutation1288; decide +kernel
  have hmoment : injectiveMoment H node1288 = injectiveMoment H pivotMatrix1288 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1288 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1288 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1288 (0 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1288 (0 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1288 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1288 (1 : Fin 4)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1288 (1 : Fin 4) = raw7993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1288 raw7993; decide +kernel
    rw [heq]
    exact (canonical7993 hH).trans (sound292 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1288 (2 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1288 (2 : Fin 4) = raw7999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1288 raw7999; decide +kernel
    rw [heq]
    exact (canonical7999 hH).trans (sound285 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1288 (3 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1288 (3 : Fin 4) = raw8003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1288 raw8003; decide +kernel
    rw [heq]
    exact (canonical8003 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1288 + (injectiveMoment H (mergeFirst pivotMatrix1288 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1288 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1288 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1288 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1288, value10, value254, value285, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1289 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1289 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem sound1289 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1289 = Sparse.eval value1289 (momentVector H) := by
  have heq : pivotMatrix1289 = (fun u v => node1289 (pivotPermutation1289 u) v) := by apply Matrix.ext; unfold pivotMatrix1289 node1289 pivotPermutation1289; decide +kernel
  have hmoment : injectiveMoment H node1289 = injectiveMoment H pivotMatrix1289 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1289 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1289 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1289 (0 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1289 (0 : Fin 4) = raw5536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1289 raw5536; decide +kernel
    rw [heq]
    exact (canonical5536 hH).trans (sound255 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1289 (1 : Fin 4)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1289 (1 : Fin 4) = raw7994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1289 raw7994; decide +kernel
    rw [heq]
    exact (canonical7994 hH).trans (sound289 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1289 (2 : Fin 4)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1289 (2 : Fin 4) = raw8000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1289 raw8000; decide +kernel
    rw [heq]
    exact (canonical8000 hH).trans (sound269 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1289 (3 : Fin 4)) =
      Sparse.eval value24 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1289 (3 : Fin 4) = raw8004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1289 raw8004; decide +kernel
    rw [heq]
    exact (canonical8004 hH).trans (sound24 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1289 + (injectiveMoment H (mergeFirst pivotMatrix1289 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1289 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1289 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1289 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1289, value24, value255, value269, value289, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1290 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem sound1290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1290 = Sparse.eval value1290 (momentVector H) := by
  have heq : pivotMatrix1290 = (fun u v => node1290 (pivotPermutation1290 u) v) := by apply Matrix.ext; unfold pivotMatrix1290 node1290 pivotPermutation1290; decide +kernel
  have hmoment : injectiveMoment H node1290 = injectiveMoment H pivotMatrix1290 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1290 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1290 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1290 (0 : Fin 4)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1290 (0 : Fin 4) = raw5942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1290 raw5942; decide +kernel
    rw [heq]
    exact (canonical5942 hH).trans (sound270 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1290 (1 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1290 (1 : Fin 4) = raw8162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1290 raw8162; decide +kernel
    rw [heq]
    exact (canonical8162 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1290 (2 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1290 (2 : Fin 4) = raw8172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1290 raw8172; decide +kernel
    rw [heq]
    exact (canonical8172 hH).trans (sound254 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1290 (3 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1290 (3 : Fin 4) = raw8183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1290 raw8183; decide +kernel
    rw [heq]
    exact (canonical8183 hH).trans (sound16 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1290 + (injectiveMoment H (mergeFirst pivotMatrix1290 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1290 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1290 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1290 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1290, value16, value254, value270, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1291 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem sound1291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1291 = Sparse.eval value1291 (momentVector H) := by
  have heq : pivotMatrix1291 = (fun u v => node1291 (pivotPermutation1291 u) v) := by apply Matrix.ext; unfold pivotMatrix1291 node1291 pivotPermutation1291; decide +kernel
  have hmoment : injectiveMoment H node1291 = injectiveMoment H pivotMatrix1291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1291 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1291 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1291 (0 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1291 (0 : Fin 4) = raw5962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1291 raw5962; decide +kernel
    rw [heq]
    exact (canonical5962 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1291 (1 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1291 (1 : Fin 4) = raw8164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1291 raw8164; decide +kernel
    rw [heq]
    exact (canonical8164 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1291 (2 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1291 (2 : Fin 4) = raw8191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1291 raw8191; decide +kernel
    rw [heq]
    exact (canonical8191 hH).trans (sound294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1291 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1291 (3 : Fin 4) = raw8195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1291 raw8195; decide +kernel
    rw [heq]
    exact (canonical8195 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1291 + (injectiveMoment H (mergeFirst pivotMatrix1291 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1291 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1291 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1291 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1291, value11, value271, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1292 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1292 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem sound1292 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1292 = Sparse.eval value1292 (momentVector H) := by
  have heq : pivotMatrix1292 = (fun u v => node1292 (pivotPermutation1292 u) v) := by apply Matrix.ext; unfold pivotMatrix1292 node1292 pivotPermutation1292; decide +kernel
  have hmoment : injectiveMoment H node1292 = injectiveMoment H pivotMatrix1292 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1292 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1292 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1292 (0 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1292 (0 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1292 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1292 (1 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1292 (1 : Fin 4) = raw8165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1292 raw8165; decide +kernel
    rw [heq]
    exact (canonical8165 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1292 (2 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1292 (2 : Fin 4) = raw8192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1292 raw8192; decide +kernel
    rw [heq]
    exact (canonical8192 hH).trans (sound284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1292 (3 : Fin 4)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1292 (3 : Fin 4) = raw8204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1292 raw8204; decide +kernel
    rw [heq]
    exact (canonical8204 hH).trans (sound46 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1292 + (injectiveMoment H (mergeFirst pivotMatrix1292 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1292 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1292 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1292 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1292, value272, value284, value291, value46, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1293 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem sound1293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1293 = Sparse.eval value1293 (momentVector H) := by
  have heq : pivotMatrix1293 = (fun u v => node1293 (pivotPermutation1293 u) v) := by apply Matrix.ext; unfold pivotMatrix1293 node1293 pivotPermutation1293; decide +kernel
  have hmoment : injectiveMoment H node1293 = injectiveMoment H pivotMatrix1293 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1293 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1293 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1293 (0 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1293 (0 : Fin 4) = raw6820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1293 raw6820; decide +kernel
    rw [heq]
    exact (canonical6820 hH).trans (sound285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1293 (1 : Fin 4)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1293 (1 : Fin 4) = raw8531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1293 raw8531; decide +kernel
    rw [heq]
    exact (canonical8531 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1293 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1293 (2 : Fin 4) = raw8578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1293 raw8578; decide +kernel
    rw [heq]
    exact (canonical8578 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1293 (3 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1293 (3 : Fin 4) = raw8646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1293 raw8646; decide +kernel
    rw [heq]
    exact (canonical8646 hH).trans (sound26 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1293 + (injectiveMoment H (mergeFirst pivotMatrix1293 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1293 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1293 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1293 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1293, value26, value271, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1294 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem sound1294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1294 = Sparse.eval value1294 (momentVector H) := by
  have heq : pivotMatrix1294 = (fun u v => node1294 (pivotPermutation1294 u) v) := by apply Matrix.ext; unfold pivotMatrix1294 node1294 pivotPermutation1294; decide +kernel
  have hmoment : injectiveMoment H node1294 = injectiveMoment H pivotMatrix1294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1294 (0 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (0 : Fin 4) = raw6845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw6845; decide +kernel
    rw [heq]
    exact (canonical6845 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1294 (1 : Fin 4)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (1 : Fin 4) = raw8537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw8537; decide +kernel
    rw [heq]
    exact (canonical8537 hH).trans (sound293 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1294 (2 : Fin 4)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (2 : Fin 4) = raw8692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw8692; decide +kernel
    rw [heq]
    exact (canonical8692 hH).trans (sound293 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1294 (3 : Fin 4)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (3 : Fin 4) = raw8711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw8711; decide +kernel
    rw [heq]
    exact (canonical8711 hH).trans (sound65 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1294 + (injectiveMoment H (mergeFirst pivotMatrix1294 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1294 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1294 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1294 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1294, value287, value293, value65, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1295 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem sound1295 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1295 = Sparse.eval value1295 (momentVector H) := by
  have heq : pivotMatrix1295 = (fun u v => node1295 (pivotPermutation1295 u) v) := by apply Matrix.ext; unfold pivotMatrix1295 node1295 pivotPermutation1295; decide +kernel
  have hmoment : injectiveMoment H node1295 = injectiveMoment H pivotMatrix1295 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1295 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1295 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1295 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1295 (0 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1295 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1295 (1 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1295 (1 : Fin 3) = raw8034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1295 raw8034; decide +kernel
    rw [heq]
    exact (canonical8034 hH).trans (sound166 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1295 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1295 (2 : Fin 3) = raw8053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1295 raw8053; decide +kernel
    rw [heq]
    exact (canonical8053 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1295 + (injectiveMoment H (mergeFirst pivotMatrix1295 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1295 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1295 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1295, value166, value201, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1296 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem sound1296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1296 = Sparse.eval value1296 (momentVector H) := by
  have heq : pivotMatrix1296 = (fun u v => node1296 (pivotPermutation1296 u) v) := by apply Matrix.ext; unfold pivotMatrix1296 node1296 pivotPermutation1296; decide +kernel
  have hmoment : injectiveMoment H node1296 = injectiveMoment H pivotMatrix1296 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1296 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1296 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1296 (0 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1296 (0 : Fin 3) = raw5800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1296 raw5800; decide +kernel
    rw [heq]
    exact (canonical5800 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1296 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1296 (1 : Fin 3) = raw8067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1296 raw8067; decide +kernel
    rw [heq]
    exact (canonical8067 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1296 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1296 (2 : Fin 3) = raw8106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1296 raw8106; decide +kernel
    rw [heq]
    exact (canonical8106 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1296 + (injectiveMoment H (mergeFirst pivotMatrix1296 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1296 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1296 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1296, value169, value226, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1297 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

theorem sound1297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1297 = Sparse.eval value1297 (momentVector H) := by
  have heq : pivotMatrix1297 = (fun u v => node1297 (pivotPermutation1297 u) v) := by apply Matrix.ext; unfold pivotMatrix1297 node1297 pivotPermutation1297; decide +kernel
  have hmoment : injectiveMoment H node1297 = injectiveMoment H pivotMatrix1297 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1297 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1297 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1297 (0 : Fin 3)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1297 (0 : Fin 3) = raw5801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1297 raw5801; decide +kernel
    rw [heq]
    exact (canonical5801 hH).trans (sound102 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1297 (1 : Fin 3)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1297 (1 : Fin 3) = raw8068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1297 raw8068; decide +kernel
    rw [heq]
    exact (canonical8068 hH).trans (sound141 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1297 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1297 (2 : Fin 3) = raw8107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1297 raw8107; decide +kernel
    rw [heq]
    exact (canonical8107 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1297 + (injectiveMoment H (mergeFirst pivotMatrix1297 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1297 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1297 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1297, value102, value141, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1298 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem sound1298 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1298 = Sparse.eval value1298 (momentVector H) := by
  have heq : pivotMatrix1298 = (fun u v => node1298 (pivotPermutation1298 u) v) := by apply Matrix.ext; unfold pivotMatrix1298 node1298 pivotPermutation1298; decide +kernel
  have hmoment : injectiveMoment H node1298 = injectiveMoment H pivotMatrix1298 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1298 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1298 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1298 (0 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1298 (0 : Fin 3) = raw6333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1298 raw6333; decide +kernel
    rw [heq]
    exact (canonical6333 hH).trans (sound244 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1298 (1 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1298 (1 : Fin 3) = raw8294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1298 raw8294; decide +kernel
    rw [heq]
    exact (canonical8294 hH).trans (sound241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1298 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1298 (2 : Fin 3) = raw8306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1298 raw8306; decide +kernel
    rw [heq]
    exact (canonical8306 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1298 + (injectiveMoment H (mergeFirst pivotMatrix1298 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1298 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1298 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1298, value241, value244, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1299 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem sound1299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1299 = Sparse.eval value1299 (momentVector H) := by
  have heq : pivotMatrix1299 = (fun u v => node1299 (pivotPermutation1299 u) v) := by apply Matrix.ext; unfold pivotMatrix1299 node1299 pivotPermutation1299; decide +kernel
  have hmoment : injectiveMoment H node1299 = injectiveMoment H pivotMatrix1299 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1299 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1299 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1299 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1299 (0 : Fin 3) = raw6559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1299 raw6559; decide +kernel
    rw [heq]
    exact (canonical6559 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1299 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1299 (1 : Fin 3) = raw8310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1299 raw8310; decide +kernel
    rw [heq]
    exact (canonical8310 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1299 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1299 (2 : Fin 3) = raw8342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1299 raw8342; decide +kernel
    rw [heq]
    exact (canonical8342 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1299 + (injectiveMoment H (mergeFirst pivotMatrix1299 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1299 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1299 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1299, value175, value181, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1300 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem sound1300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1300 = Sparse.eval value1300 (momentVector H) := by
  have heq : pivotMatrix1300 = (fun u v => node1300 (pivotPermutation1300 u) v) := by apply Matrix.ext; unfold pivotMatrix1300 node1300 pivotPermutation1300; decide +kernel
  have hmoment : injectiveMoment H node1300 = injectiveMoment H pivotMatrix1300 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1300 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1300 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1300 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1300 (0 : Fin 3) = raw7124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1300 raw7124; decide +kernel
    rw [heq]
    exact (canonical7124 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1300 (1 : Fin 3)) =
      Sparse.eval value195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1300 (1 : Fin 3) = raw9066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1300 raw9066; decide +kernel
    rw [heq]
    exact (canonical9066 hH).trans (sound195 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1300 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1300 (2 : Fin 3) = raw9080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1300 raw9080; decide +kernel
    rw [heq]
    exact (canonical9080 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1300 + (injectiveMoment H (mergeFirst pivotMatrix1300 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1300 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1300 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1300, value195, value201, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1301 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem sound1301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1301 = Sparse.eval value1301 (momentVector H) := by
  have heq : pivotMatrix1301 = (fun u v => node1301 (pivotPermutation1301 u) v) := by apply Matrix.ext; unfold pivotMatrix1301 node1301 pivotPermutation1301; decide +kernel
  have hmoment : injectiveMoment H node1301 = injectiveMoment H pivotMatrix1301 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1301 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1301 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1301 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1301 (0 : Fin 3) = raw7247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1301 raw7247; decide +kernel
    rw [heq]
    exact (canonical7247 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1301 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1301 (1 : Fin 3) = raw9090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1301 raw9090; decide +kernel
    rw [heq]
    exact (canonical9090 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1301 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1301 (2 : Fin 3) = raw9176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1301 raw9176; decide +kernel
    rw [heq]
    exact (canonical9176 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1301 + (injectiveMoment H (mergeFirst pivotMatrix1301 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1301 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1301 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1301, value169, value185, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1302 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

theorem sound1302 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1302 = Sparse.eval value1302 (momentVector H) := by
  have heq : pivotMatrix1302 = (fun u v => node1302 (pivotPermutation1302 u) v) := by apply Matrix.ext; unfold pivotMatrix1302 node1302 pivotPermutation1302; decide +kernel
  have hmoment : injectiveMoment H node1302 = injectiveMoment H pivotMatrix1302 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1302 0 = Pi.single (2 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1302 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1302 (0 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1302 (0 : Fin 3) = raw7248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1302 raw7248; decide +kernel
    rw [heq]
    exact (canonical7248 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1302 (1 : Fin 3)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1302 (1 : Fin 3) = raw9091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1302 raw9091; decide +kernel
    rw [heq]
    exact (canonical9091 hH).trans (sound140 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1302 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1302 (2 : Fin 3) = raw9177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1302 raw9177; decide +kernel
    rw [heq]
    exact (canonical9177 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1302 + (injectiveMoment H (mergeFirst pivotMatrix1302 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1302 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1302 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1302, value140, value153, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1303 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, -1, 1, -2], ![-1, 3, -3, 1]]

theorem sound1303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1303 = Sparse.eval value1303 (momentVector H) := by
  have heq : pivotMatrix1303 = (fun u v => node1303.transpose (pivotPermutation1303 u) v) := by apply Matrix.ext; unfold pivotMatrix1303 node1303 pivotPermutation1303; decide +kernel
  have hmoment : injectiveMoment H node1303 = injectiveMoment H pivotMatrix1303 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1303 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1303 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1303 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1303 (0 : Fin 3) = raw5849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1303 raw5849; decide +kernel
    rw [heq]
    exact (canonical5849 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1303 (1 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1303 (1 : Fin 3) = raw8262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1303 raw8262; decide +kernel
    rw [heq]
    exact (canonical8262 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1303 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1303 (2 : Fin 3) = raw8266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1303 raw8266; decide +kernel
    rw [heq]
    exact (canonical8266 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1303 + (injectiveMoment H (mergeFirst pivotMatrix1303 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1303 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1303 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1303, value159, value162, value168, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1304 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, 0, 0, -2], ![-1, 2, -2, 1]]

theorem sound1304 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1304 = Sparse.eval value1304 (momentVector H) := by
  have heq : pivotMatrix1304 = (fun u v => node1304.transpose (pivotPermutation1304 u) v) := by apply Matrix.ext; unfold pivotMatrix1304 node1304 pivotPermutation1304; decide +kernel
  have hmoment : injectiveMoment H node1304 = injectiveMoment H pivotMatrix1304 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1304 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1304 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1304 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1304 (0 : Fin 3) = raw5850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1304 raw5850; decide +kernel
    rw [heq]
    exact (canonical5850 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1304 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1304 (1 : Fin 3) = raw8263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1304 raw8263; decide +kernel
    rw [heq]
    exact (canonical8263 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1304 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1304 (2 : Fin 3) = raw8267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1304 raw8267; decide +kernel
    rw [heq]
    exact (canonical8267 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1304 + (injectiveMoment H (mergeFirst pivotMatrix1304 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1304 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1304 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1304, value197, value224, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1305 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![2, 0, 1, -3], ![-1, 2, -3, 2]]

theorem sound1305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1305 = Sparse.eval value1305 (momentVector H) := by
  have heq : pivotMatrix1305 = (fun u v => node1305.transpose (pivotPermutation1305 u) v) := by apply Matrix.ext; unfold pivotMatrix1305 node1305 pivotPermutation1305; decide +kernel
  have hmoment : injectiveMoment H node1305 = injectiveMoment H pivotMatrix1305 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1305 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1305 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1305 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1305 (0 : Fin 3) = raw5851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1305 raw5851; decide +kernel
    rw [heq]
    exact (canonical5851 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1305 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1305 (1 : Fin 3) = raw8264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1305 raw8264; decide +kernel
    rw [heq]
    exact (canonical8264 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1305 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1305 (2 : Fin 3) = raw8268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1305 raw8268; decide +kernel
    rw [heq]
    exact (canonical8268 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1305 + (injectiveMoment H (mergeFirst pivotMatrix1305 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1305 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1305 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1305, value103, value163, value169, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1306 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -3, 0, 1], ![-1, 4, -2, -1]]

theorem sound1306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1306 = Sparse.eval value1306 (momentVector H) := by
  have heq : pivotMatrix1306 = (fun u v => node1306.transpose (pivotPermutation1306 u) v) := by apply Matrix.ext; unfold pivotMatrix1306 node1306 pivotPermutation1306; decide +kernel
  have hmoment : injectiveMoment H node1306 = injectiveMoment H pivotMatrix1306 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1306 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1306 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1306 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1306 (0 : Fin 3) = raw6947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1306 raw6947; decide +kernel
    rw [heq]
    exact (canonical6947 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1306 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1306 (1 : Fin 3) = raw8925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1306 raw8925; decide +kernel
    rw [heq]
    exact (canonical8925 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1306 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1306 (2 : Fin 3) = raw8930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1306 raw8930; decide +kernel
    rw [heq]
    exact (canonical8930 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1306 + (injectiveMoment H (mergeFirst pivotMatrix1306 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1306 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1306 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1306, value201, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1307 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1307 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3]]

theorem sound1307 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1307 = Sparse.eval value1307 (momentVector H) := by
  have heq : pivotMatrix1307 = (fun u v => node1307 (pivotPermutation1307 u) v) := by apply Matrix.ext; unfold pivotMatrix1307 node1307 pivotPermutation1307; decide +kernel
  have hmoment : injectiveMoment H node1307 = injectiveMoment H pivotMatrix1307 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1307 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1307 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1307 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1307 (0 : Fin 3) = raw8914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1307 raw8914; decide +kernel
    rw [heq]
    exact (canonical8914 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1307 (1 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1307 (1 : Fin 3) = raw7599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1307 raw7599; decide +kernel
    rw [heq]
    exact (canonical7599 hH).trans (sound166 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1307 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1307 (2 : Fin 3) = raw7561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1307 raw7561; decide +kernel
    rw [heq]
    exact (canonical7561 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1307 + (injectiveMoment H (mergeFirst pivotMatrix1307 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1307 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1307 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1307, value166, value173, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1308 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -2, 1, -1], ![-1, 3, -3, 1]]

theorem sound1308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1308 = Sparse.eval value1308 (momentVector H) := by
  have heq : pivotMatrix1308 = (fun u v => node1308.transpose (pivotPermutation1308 u) v) := by apply Matrix.ext; unfold pivotMatrix1308 node1308 pivotPermutation1308; decide +kernel
  have hmoment : injectiveMoment H node1308 = injectiveMoment H pivotMatrix1308 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1308 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1308 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1308 (0 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1308 (0 : Fin 3) = raw6948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1308 raw6948; decide +kernel
    rw [heq]
    exact (canonical6948 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1308 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1308 (1 : Fin 3) = raw8926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1308 raw8926; decide +kernel
    rw [heq]
    exact (canonical8926 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1308 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1308 (2 : Fin 3) = raw8932 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1308 raw8932; decide +kernel
    rw [heq]
    exact (canonical8932 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1308 + (injectiveMoment H (mergeFirst pivotMatrix1308 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1308 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1308 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1308, value167, value174, value180, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1309 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

theorem sound1309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1309 = Sparse.eval value1309 (momentVector H) := by
  have heq : pivotMatrix1309 = (fun u v => node1309.transpose (pivotPermutation1309 u) v) := by apply Matrix.ext; unfold pivotMatrix1309 node1309 pivotPermutation1309; decide +kernel
  have hmoment : injectiveMoment H node1309 = injectiveMoment H pivotMatrix1309 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1309 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1309 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1309 (0 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1309 (0 : Fin 3) = raw6949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1309 raw6949; decide +kernel
    rw [heq]
    exact (canonical6949 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1309 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1309 (1 : Fin 3) = raw8927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1309 raw8927; decide +kernel
    rw [heq]
    exact (canonical8927 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1309 (2 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1309 (2 : Fin 3) = raw8933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1309 raw8933; decide +kernel
    rw [heq]
    exact (canonical8933 hH).trans (sound202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1309 + (injectiveMoment H (mergeFirst pivotMatrix1309 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1309 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1309 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1309, value202, value210, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1310 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, -1, 1, -2], ![-1, 2, -3, 2]]

theorem sound1310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1310 = Sparse.eval value1310 (momentVector H) := by
  have heq : pivotMatrix1310 = (fun u v => node1310.transpose (pivotPermutation1310 u) v) := by apply Matrix.ext; unfold pivotMatrix1310 node1310 pivotPermutation1310; decide +kernel
  have hmoment : injectiveMoment H node1310 = injectiveMoment H pivotMatrix1310 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1310 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1310 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1310 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (0 : Fin 3) = raw6950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw6950; decide +kernel
    rw [heq]
    exact (canonical6950 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1310 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (1 : Fin 3) = raw8928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw8928; decide +kernel
    rw [heq]
    exact (canonical8928 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1310 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (2 : Fin 3) = raw8934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw8934; decide +kernel
    rw [heq]
    exact (canonical8934 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1310 + (injectiveMoment H (mergeFirst pivotMatrix1310 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1310 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1310 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1310, value167, value175, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1311 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1311 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem sound1311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1311 = Sparse.eval value1311 (momentVector H) := by
  have heq : pivotMatrix1311 = (fun u v => node1311 (pivotPermutation1311 u) v) := by apply Matrix.ext; unfold pivotMatrix1311 node1311 pivotPermutation1311; decide +kernel
  have hmoment : injectiveMoment H node1311 = injectiveMoment H pivotMatrix1311 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1311 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1311 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1311 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (0 : Fin 3) = raw6935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw6935; decide +kernel
    rw [heq]
    exact (canonical6935 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1311 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (1 : Fin 3) = raw7585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw7585; decide +kernel
    rw [heq]
    exact (canonical7585 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1311 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1311 + (injectiveMoment H (mergeFirst pivotMatrix1311 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1311 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1311 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1311, value169, value203, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1312 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1312 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem sound1312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1312 = Sparse.eval value1312 (momentVector H) := by
  have heq : pivotMatrix1312 = (fun u v => node1312 (pivotPermutation1312 u) v) := by apply Matrix.ext; unfold pivotMatrix1312 node1312 pivotPermutation1312; decide +kernel
  have hmoment : injectiveMoment H node1312 = injectiveMoment H pivotMatrix1312 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1312 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1312 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1312 (0 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1312 (0 : Fin 3) = raw6936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1312 raw6936; decide +kernel
    rw [heq]
    exact (canonical6936 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1312 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1312 (1 : Fin 3) = raw7587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1312 raw7587; decide +kernel
    rw [heq]
    exact (canonical7587 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1312 (2 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1312 (2 : Fin 3) = raw7592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1312 raw7592; decide +kernel
    rw [heq]
    exact (canonical7592 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1312 + (injectiveMoment H (mergeFirst pivotMatrix1312 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1312 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1312 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1312, value166, value174, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1313 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, -3, 1, 0], ![-1, 3, -3, 1]]

theorem sound1313 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1313 = Sparse.eval value1313 (momentVector H) := by
  have heq : pivotMatrix1313 = (fun u v => node1313.transpose (pivotPermutation1313 u) v) := by apply Matrix.ext; unfold pivotMatrix1313 node1313 pivotPermutation1313; decide +kernel
  have hmoment : injectiveMoment H node1313 = injectiveMoment H pivotMatrix1313 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1313 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1313 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1313 (0 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1313 (0 : Fin 3) = raw7604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1313 raw7604; decide +kernel
    rw [heq]
    exact (canonical7604 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1313 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1313 (1 : Fin 3) = raw9985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1313 raw9985; decide +kernel
    rw [heq]
    exact (canonical9985 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1313 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1313 (2 : Fin 3) = raw9989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1313 raw9989; decide +kernel
    rw [heq]
    exact (canonical9989 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1313 + (injectiveMoment H (mergeFirst pivotMatrix1313 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1313 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1313 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1313, value163, value170, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1314 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, -2, 0, 0], ![-1, 2, -2, 1]]

theorem sound1314 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1314 = Sparse.eval value1314 (momentVector H) := by
  have heq : pivotMatrix1314 = (fun u v => node1314.transpose (pivotPermutation1314 u) v) := by apply Matrix.ext; unfold pivotMatrix1314 node1314 pivotPermutation1314; decide +kernel
  have hmoment : injectiveMoment H node1314 = injectiveMoment H pivotMatrix1314 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1314 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1314 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1314 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1314 (0 : Fin 3) = raw7605 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1314 raw7605; decide +kernel
    rw [heq]
    exact (canonical7605 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1314 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1314 (1 : Fin 3) = raw9986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1314 raw9986; decide +kernel
    rw [heq]
    exact (canonical9986 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1314 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1314 (2 : Fin 3) = raw9990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1314 raw9990; decide +kernel
    rw [heq]
    exact (canonical9990 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1314 + (injectiveMoment H (mergeFirst pivotMatrix1314 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1314 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1314 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1314, value197, value203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1315 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, -2, 1, -1], ![-1, 2, -3, 2]]

theorem sound1315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1315 = Sparse.eval value1315 (momentVector H) := by
  have heq : pivotMatrix1315 = (fun u v => node1315.transpose (pivotPermutation1315 u) v) := by apply Matrix.ext; unfold pivotMatrix1315 node1315 pivotPermutation1315; decide +kernel
  have hmoment : injectiveMoment H node1315 = injectiveMoment H pivotMatrix1315 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1315 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1315 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (0 : Fin 3) = raw7606 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw7606; decide +kernel
    rw [heq]
    exact (canonical7606 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (1 : Fin 3) = raw9987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9987; decide +kernel
    rw [heq]
    exact (canonical9987 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (2 : Fin 3) = raw9991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9991; decide +kernel
    rw [heq]
    exact (canonical9991 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1315 + (injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1315, value162, value169, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1316 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1316 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem sound1316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1316 = Sparse.eval value1316 (momentVector H) := by
  have heq : pivotMatrix1316 = (fun u v => node1316 (pivotPermutation1316 u) v) := by apply Matrix.ext; unfold pivotMatrix1316 node1316 pivotPermutation1316; decide +kernel
  have hmoment : injectiveMoment H node1316 = injectiveMoment H pivotMatrix1316 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1316 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1316 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1316 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (0 : Fin 3) = raw7511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7511; decide +kernel
    rw [heq]
    exact (canonical7511 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1316 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (1 : Fin 3) = raw7590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7590; decide +kernel
    rw [heq]
    exact (canonical7590 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1316 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1316 + (injectiveMoment H (mergeFirst pivotMatrix1316 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1316 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1316 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1316, value169, value210, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1317 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1317 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

theorem sound1317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1317 = Sparse.eval value1317 (momentVector H) := by
  have heq : pivotMatrix1317 = (fun u v => node1317 (pivotPermutation1317 u) v) := by apply Matrix.ext; unfold pivotMatrix1317 node1317 pivotPermutation1317; decide +kernel
  have hmoment : injectiveMoment H node1317 = injectiveMoment H pivotMatrix1317 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1317 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1317 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1317 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (0 : Fin 3) = raw7512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7512; decide +kernel
    rw [heq]
    exact (canonical7512 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1317 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (1 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1317 (2 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (2 : Fin 3) = raw7592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7592; decide +kernel
    rw [heq]
    exact (canonical7592 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1317 + (injectiveMoment H (mergeFirst pivotMatrix1317 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1317 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1317 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1317, value166, value169, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1318 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -2, 0, -1], ![-2, 3, -2, 1]]

theorem sound1318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1318 = Sparse.eval value1318 (momentVector H) := by
  have heq : pivotMatrix1318 = (fun u v => node1318.transpose (pivotPermutation1318 u) v) := by apply Matrix.ext; unfold pivotMatrix1318 node1318 pivotPermutation1318; decide +kernel
  have hmoment : injectiveMoment H node1318 = injectiveMoment H pivotMatrix1318 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1318 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1318 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1318 (0 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1318 (0 : Fin 3) = raw6951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1318 raw6951; decide +kernel
    rw [heq]
    exact (canonical6951 hH).trans (sound209 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1318 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1318 (1 : Fin 3) = raw8931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1318 raw8931; decide +kernel
    rw [heq]
    exact (canonical8931 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1318 (2 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1318 (2 : Fin 3) = raw8935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1318 raw8935; decide +kernel
    rw [heq]
    exact (canonical8935 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1318 + (injectiveMoment H (mergeFirst pivotMatrix1318 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1318 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1318 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1318, value169, value196, value209, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1319 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -1, 0, -2], ![-2, 2, -2, 2]]

theorem sound1319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1319 = Sparse.eval value1319 (momentVector H) := by
  have heq : pivotMatrix1319 = (fun u v => node1319.transpose (pivotPermutation1319 u) v) := by apply Matrix.ext; unfold pivotMatrix1319 node1319 pivotPermutation1319; decide +kernel
  have hmoment : injectiveMoment H node1319 = injectiveMoment H pivotMatrix1319 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1319 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1319 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1319 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1319 (0 : Fin 3) = raw6952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1319 raw6952; decide +kernel
    rw [heq]
    exact (canonical6952 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1319 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1319 (1 : Fin 3) = raw8933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1319 raw8933; decide +kernel
    rw [heq]
    exact (canonical8933 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1319 (2 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1319 (2 : Fin 3) = raw8936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1319 raw8936; decide +kernel
    rw [heq]
    exact (canonical8936 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1319 + (injectiveMoment H (mergeFirst pivotMatrix1319 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1319 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1319 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1319, value196, value202, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1320 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1320 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem sound1320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1320 = Sparse.eval value1320 (momentVector H) := by
  have heq : pivotMatrix1320 = (fun u v => node1320 (pivotPermutation1320 u) v) := by apply Matrix.ext; unfold pivotMatrix1320 node1320 pivotPermutation1320; decide +kernel
  have hmoment : injectiveMoment H node1320 = injectiveMoment H pivotMatrix1320 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1320 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1320 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1320 (0 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1320 (0 : Fin 3) = raw6968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1320 raw6968; decide +kernel
    rw [heq]
    exact (canonical6968 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1320 (1 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1320 (1 : Fin 3) = raw7616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1320 raw7616; decide +kernel
    rw [heq]
    exact (canonical7616 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1320 (2 : Fin 3)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1320 (2 : Fin 3) = raw7617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1320 raw7617; decide +kernel
    rw [heq]
    exact (canonical7617 hH).trans (sound141 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1320 + (injectiveMoment H (mergeFirst pivotMatrix1320 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1320 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1320 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1320, value141, value170, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1321 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![3, -3, 0, 0], ![-2, 3, -2, 1]]

theorem sound1321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1321 = Sparse.eval value1321 (momentVector H) := by
  have heq : pivotMatrix1321 = (fun u v => node1321.transpose (pivotPermutation1321 u) v) := by apply Matrix.ext; unfold pivotMatrix1321 node1321 pivotPermutation1321; decide +kernel
  have hmoment : injectiveMoment H node1321 = injectiveMoment H pivotMatrix1321 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1321 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1321 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1321 (0 : Fin 3)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1321 (0 : Fin 3) = raw7607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1321 raw7607; decide +kernel
    rw [heq]
    exact (canonical7607 hH).trans (sound214 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1321 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1321 (1 : Fin 3) = raw9988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1321 raw9988; decide +kernel
    rw [heq]
    exact (canonical9988 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1321 (2 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1321 (2 : Fin 3) = raw9992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1321 raw9992; decide +kernel
    rw [heq]
    exact (canonical9992 hH).trans (sound192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1321 + (injectiveMoment H (mergeFirst pivotMatrix1321 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1321 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1321 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1321, value192, value198, value214, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1322 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![3, -2, 0, -1], ![-2, 2, -2, 2]]

theorem sound1322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1322 = Sparse.eval value1322 (momentVector H) := by
  have heq : pivotMatrix1322 = (fun u v => node1322.transpose (pivotPermutation1322 u) v) := by apply Matrix.ext; unfold pivotMatrix1322 node1322 pivotPermutation1322; decide +kernel
  have hmoment : injectiveMoment H node1322 = injectiveMoment H pivotMatrix1322 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1322 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1322 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1322 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1322 (0 : Fin 3) = raw7608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1322 raw7608; decide +kernel
    rw [heq]
    exact (canonical7608 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1322 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1322 (1 : Fin 3) = raw9990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1322 raw9990; decide +kernel
    rw [heq]
    exact (canonical9990 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1322 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1322 (2 : Fin 3) = raw9993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1322 raw9993; decide +kernel
    rw [heq]
    exact (canonical9993 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1322 + (injectiveMoment H (mergeFirst pivotMatrix1322 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1322 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1322 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1322, value163, value197, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1323 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1323 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem sound1323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1323 = Sparse.eval value1323 (momentVector H) := by
  have heq : pivotMatrix1323 = (fun u v => node1323 (pivotPermutation1323 u) v) := by apply Matrix.ext; unfold pivotMatrix1323 node1323 pivotPermutation1323; decide +kernel
  have hmoment : injectiveMoment H node1323 = injectiveMoment H pivotMatrix1323 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1323 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1323 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1323 (0 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (0 : Fin 5) = raw5139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw5139; decide +kernel
    rw [heq]
    exact (canonical5139 hH).trans (sound232 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1323 (1 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (1 : Fin 5) = raw7634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7634; decide +kernel
    rw [heq]
    exact (canonical7634 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1323 (2 : Fin 5)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (2 : Fin 5) = raw7670 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7670; decide +kernel
    rw [heq]
    exact (canonical7670 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1323 (3 : Fin 5)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (3 : Fin 5) = raw7677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7677; decide +kernel
    rw [heq]
    exact (canonical7677 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1323 (4 : Fin 5)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (4 : Fin 5) = raw7679 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7679; decide +kernel
    rw [heq]
    exact (canonical7679 hH).trans (sound65 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1323 + (injectiveMoment H (mergeFirst pivotMatrix1323 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1323, value232, value65, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1324 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-4, 2, 1, 1], ![4, -1, -2, -1]]

theorem sound1324 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1324 = Sparse.eval value1324 (momentVector H) := by
  have heq : pivotMatrix1324 = (fun u v => node1324.transpose (pivotPermutation1324 u) v) := by apply Matrix.ext; unfold pivotMatrix1324 node1324 pivotPermutation1324; decide +kernel
  have hmoment : injectiveMoment H node1324 = injectiveMoment H pivotMatrix1324 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1324 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1324 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1324 (0 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1324 (0 : Fin 3) = raw8797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1324 raw8797; decide +kernel
    rw [heq]
    exact (canonical8797 hH).trans (sound286 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1324 (1 : Fin 3)) =
      Sparse.eval value234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1324 (1 : Fin 3) = raw10115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1324 raw10115; decide +kernel
    rw [heq]
    exact (canonical10115 hH).trans (sound234 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1324 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1324 (2 : Fin 3) = raw10116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1324 raw10116; decide +kernel
    rw [heq]
    exact (canonical10116 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1324 + (injectiveMoment H (mergeFirst pivotMatrix1324 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1324 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1324 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1324, value234, value246, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1325 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-4, 2, 1, 1], ![4, -2, -2, 0]]

theorem sound1325 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1325 = Sparse.eval value1325 (momentVector H) := by
  have heq : pivotMatrix1325 = (fun u v => node1325.transpose (pivotPermutation1325 u) v) := by apply Matrix.ext; unfold pivotMatrix1325 node1325 pivotPermutation1325; decide +kernel
  have hmoment : injectiveMoment H node1325 = injectiveMoment H pivotMatrix1325 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1325 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1325 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1325 (0 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1325 (0 : Fin 3) = raw9736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1325 raw9736; decide +kernel
    rw [heq]
    exact (canonical9736 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1325 (1 : Fin 3)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1325 (1 : Fin 3) = raw10145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1325 raw10145; decide +kernel
    rw [heq]
    exact (canonical10145 hH).trans (sound200 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1325 (2 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1325 (2 : Fin 3) = raw10146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1325 raw10146; decide +kernel
    rw [heq]
    exact (canonical10146 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1325 + (injectiveMoment H (mergeFirst pivotMatrix1325 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1325 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1325 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1325, value200, value225, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1326 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1326 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem sound1326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1326 = Sparse.eval value1326 (momentVector H) := by
  have heq : pivotMatrix1326 = (fun u v => node1326 (pivotPermutation1326 u) v) := by apply Matrix.ext; unfold pivotMatrix1326 node1326 pivotPermutation1326; decide +kernel
  have hmoment : injectiveMoment H node1326 = injectiveMoment H pivotMatrix1326 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1326 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1326 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1326 (0 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1326 (0 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1326 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1326 (1 : Fin 3)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1326 (1 : Fin 3) = raw7781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1326 raw7781; decide +kernel
    rw [heq]
    exact (canonical7781 hH).trans (sound267 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1326 (2 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1326 (2 : Fin 3) = raw7786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1326 raw7786; decide +kernel
    rw [heq]
    exact (canonical7786 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1326 + (injectiveMoment H (mergeFirst pivotMatrix1326 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1326 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1326 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1326, value149, value180, value267, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1327 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-3, 3, 1, -1], ![3, -2, -2, 1]]

theorem sound1327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1327 = Sparse.eval value1327 (momentVector H) := by
  have heq : pivotMatrix1327 = (fun u v => node1327.transpose (pivotPermutation1327 u) v) := by apply Matrix.ext; unfold pivotMatrix1327 node1327 pivotPermutation1327; decide +kernel
  have hmoment : injectiveMoment H node1327 = injectiveMoment H pivotMatrix1327 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1327 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1327 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1327 (0 : Fin 3)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1327 (0 : Fin 3) = raw8801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1327 raw8801; decide +kernel
    rw [heq]
    exact (canonical8801 hH).trans (sound273 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1327 (1 : Fin 3)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1327 (1 : Fin 3) = raw10117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1327 raw10117; decide +kernel
    rw [heq]
    exact (canonical10117 hH).trans (sound245 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1327 (2 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1327 (2 : Fin 3) = raw10121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1327 raw10121; decide +kernel
    rw [heq]
    exact (canonical10121 hH).trans (sound260 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1327 + (injectiveMoment H (mergeFirst pivotMatrix1327 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1327 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1327 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1327, value245, value260, value273, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1328 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1328 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -3, 3], ![0, 0, 2, -2], ![1, -1, 2, -2]]

theorem sound1328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1328 = Sparse.eval value1328 (momentVector H) := by
  have heq : pivotMatrix1328 = (fun u v => node1328 (pivotPermutation1328 u) v) := by apply Matrix.ext; unfold pivotMatrix1328 node1328 pivotPermutation1328; decide +kernel
  have hmoment : injectiveMoment H node1328 = injectiveMoment H pivotMatrix1328 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1328 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1328 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1328 (0 : Fin 3)) =
      Sparse.eval value139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1328 (0 : Fin 3) = raw7762 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1328 raw7762; decide +kernel
    rw [heq]
    exact (canonical7762 hH).trans (sound139 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1328 (1 : Fin 3)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1328 (1 : Fin 3) = raw7781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1328 raw7781; decide +kernel
    rw [heq]
    exact (canonical7781 hH).trans (sound267 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1328 (2 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1328 (2 : Fin 3) = raw7783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1328 raw7783; decide +kernel
    rw [heq]
    exact (canonical7783 hH).trans (sound168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1328 + (injectiveMoment H (mergeFirst pivotMatrix1328 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1328 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1328 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1328, value139, value168, value267, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1329 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 2, 1, 0], ![3, -2, -2, 1]]

theorem sound1329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1329 = Sparse.eval value1329 (momentVector H) := by
  have heq : pivotMatrix1329 = (fun u v => node1329.transpose (pivotPermutation1329 u) v) := by apply Matrix.ext; unfold pivotMatrix1329 node1329 pivotPermutation1329; decide +kernel
  have hmoment : injectiveMoment H node1329 = injectiveMoment H pivotMatrix1329 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1329 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1329 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1329 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1329 (0 : Fin 3) = raw9739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1329 raw9739; decide +kernel
    rw [heq]
    exact (canonical9739 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1329 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1329 (1 : Fin 3) = raw10146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1329 raw10146; decide +kernel
    rw [heq]
    exact (canonical10146 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1329 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1329 (2 : Fin 3) = raw10147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1329 raw10147; decide +kernel
    rw [heq]
    exact (canonical10147 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1329 + (injectiveMoment H (mergeFirst pivotMatrix1329 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1329 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1329 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1329, value212, value225, value280, Sparse.eval] at hc ⊢
  linarith

theorem sound1330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1330 = Sparse.eval value1330 (momentVector H) := by
  have hc : momentVector H 253 = injectiveMoment H node1330 := rfl
  simp [value1330, Sparse.eval, hc]

def pivotPermutation1331 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 1, 2], ![2, 2, -2, -2]]

theorem sound1331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1331 = Sparse.eval value1331 (momentVector H) := by
  have heq : pivotMatrix1331 = (fun u v => node1331.transpose (pivotPermutation1331 u) v) := by apply Matrix.ext; unfold pivotMatrix1331 node1331 pivotPermutation1331; decide +kernel
  have hmoment : injectiveMoment H node1331 = injectiveMoment H pivotMatrix1331 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1331 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1331 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1331 (0 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1331 (0 : Fin 3) = raw8802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1331 raw8802; decide +kernel
    rw [heq]
    exact (canonical8802 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1331 (1 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1331 (1 : Fin 3) = raw10118 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1331 raw10118; decide +kernel
    rw [heq]
    exact (canonical10118 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1331 (2 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1331 (2 : Fin 3) = raw10123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1331 raw10123; decide +kernel
    rw [heq]
    exact (canonical10123 hH).trans (sound276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1331 + (injectiveMoment H (mergeFirst pivotMatrix1331 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1331 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1331 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1331, value260, value276, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1332 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 2, 1], ![2, 2, -3, -1]]

theorem sound1332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1332 = Sparse.eval value1332 (momentVector H) := by
  have heq : pivotMatrix1332 = (fun u v => node1332.transpose (pivotPermutation1332 u) v) := by apply Matrix.ext; unfold pivotMatrix1332 node1332 pivotPermutation1332; decide +kernel
  have hmoment : injectiveMoment H node1332 = injectiveMoment H pivotMatrix1332 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1332 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1332 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1332 (0 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1332 (0 : Fin 3) = raw8803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1332 raw8803; decide +kernel
    rw [heq]
    exact (canonical8803 hH).trans (sound268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1332 (1 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1332 (1 : Fin 3) = raw10119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1332 raw10119; decide +kernel
    rw [heq]
    exact (canonical10119 hH).trans (sound262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1332 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1332 (2 : Fin 3) = raw10124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1332 raw10124; decide +kernel
    rw [heq]
    exact (canonical10124 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1332 + (injectiveMoment H (mergeFirst pivotMatrix1332 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1332 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1332 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1332, value261, value262, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1333 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1333 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, 2, 1, -1], ![2, -1, -2, 1]]

theorem sound1333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1333 = Sparse.eval value1333 (momentVector H) := by
  have heq : pivotMatrix1333 = (fun u v => node1333.transpose (pivotPermutation1333 u) v) := by apply Matrix.ext; unfold pivotMatrix1333 node1333 pivotPermutation1333; decide +kernel
  have hmoment : injectiveMoment H node1333 = injectiveMoment H pivotMatrix1333 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1333 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1333 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1333 (0 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1333 (0 : Fin 3) = raw8805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1333 raw8805; decide +kernel
    rw [heq]
    exact (canonical8805 hH).trans (sound288 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1333 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1333 (1 : Fin 3) = raw10120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1333 raw10120; decide +kernel
    rw [heq]
    exact (canonical10120 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1333 (2 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1333 (2 : Fin 3) = raw10126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1333 raw10126; decide +kernel
    rw [heq]
    exact (canonical10126 hH).trans (sound276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1333 + (injectiveMoment H (mergeFirst pivotMatrix1333 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1333 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1333 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1333, value261, value276, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1334 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1334 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 1, -2, 2], ![0, -1, 3, -2], ![1, -1, -1, 1]]

theorem sound1334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1334 = Sparse.eval value1334 (momentVector H) := by
  have heq : pivotMatrix1334 = (fun u v => node1334 (pivotPermutation1334 u) v) := by apply Matrix.ext; unfold pivotMatrix1334 node1334 pivotPermutation1334; decide +kernel
  have hmoment : injectiveMoment H node1334 = injectiveMoment H pivotMatrix1334 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1334 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1334 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1334 (0 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1334 (0 : Fin 3) = raw7961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1334 raw7961; decide +kernel
    rw [heq]
    exact (canonical7961 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1334 (1 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1334 (1 : Fin 3) = raw7827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1334 raw7827; decide +kernel
    rw [heq]
    exact (canonical7827 hH).trans (sound259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1334 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1334 (2 : Fin 3) = raw7815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1334 raw7815; decide +kernel
    rw [heq]
    exact (canonical7815 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1334 + (injectiveMoment H (mergeFirst pivotMatrix1334 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1334 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1334 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1334, value259, value261, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1335 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1335 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem sound1335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1335 = Sparse.eval value1335 (momentVector H) := by
  have heq : pivotMatrix1335 = (fun u v => node1335 (pivotPermutation1335 u) v) := by apply Matrix.ext; unfold pivotMatrix1335 node1335 pivotPermutation1335; decide +kernel
  have hmoment : injectiveMoment H node1335 = injectiveMoment H pivotMatrix1335 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1335 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1335 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1335 (0 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1335 (0 : Fin 3) = raw7783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1335 raw7783; decide +kernel
    rw [heq]
    exact (canonical7783 hH).trans (sound168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1335 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1335 (1 : Fin 3) = raw7823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1335 raw7823; decide +kernel
    rw [heq]
    exact (canonical7823 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1335 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1335 (2 : Fin 3) = raw7824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1335 raw7824; decide +kernel
    rw [heq]
    exact (canonical7824 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1335 + (injectiveMoment H (mergeFirst pivotMatrix1335 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1335 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1335 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1335, value168, value283, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1336 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1336 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem sound1336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1336 = Sparse.eval value1336 (momentVector H) := by
  have heq : pivotMatrix1336 = (fun u v => node1336 (pivotPermutation1336 u) v) := by apply Matrix.ext; unfold pivotMatrix1336 node1336 pivotPermutation1336; decide +kernel
  have hmoment : injectiveMoment H node1336 = injectiveMoment H pivotMatrix1336 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1336 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1336 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1336 (0 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1336 (0 : Fin 3) = raw7786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1336 raw7786; decide +kernel
    rw [heq]
    exact (canonical7786 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1336 (1 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1336 (1 : Fin 3) = raw7828 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1336 raw7828; decide +kernel
    rw [heq]
    exact (canonical7828 hH).trans (sound288 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1336 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1336 (2 : Fin 3) = raw7829 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1336 raw7829; decide +kernel
    rw [heq]
    exact (canonical7829 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1336 + (injectiveMoment H (mergeFirst pivotMatrix1336 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1336 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1336 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1336, value180, value210, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1337 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1337 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 1, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

theorem sound1337 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1337 = Sparse.eval value1337 (momentVector H) := by
  have heq : pivotMatrix1337 = (fun u v => node1337 (pivotPermutation1337 u) v) := by apply Matrix.ext; unfold pivotMatrix1337 node1337 pivotPermutation1337; decide +kernel
  have hmoment : injectiveMoment H node1337 = injectiveMoment H pivotMatrix1337 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1337 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1337 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1337 (0 : Fin 3)) =
      Sparse.eval value105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1337 (0 : Fin 3) = raw7964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1337 raw7964; decide +kernel
    rw [heq]
    exact (canonical7964 hH).trans (sound105 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1337 (1 : Fin 3)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1337 (1 : Fin 3) = raw7830 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1337 raw7830; decide +kernel
    rw [heq]
    exact (canonical7830 hH).trans (sound132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1337 (2 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1337 (2 : Fin 3) = raw7827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1337 raw7827; decide +kernel
    rw [heq]
    exact (canonical7827 hH).trans (sound259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1337 + (injectiveMoment H (mergeFirst pivotMatrix1337 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1337 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1337 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1337, value105, value132, value259, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1338 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1338 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 4, -2, 0], ![2, -4, 1, 1]]

theorem sound1338 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1338 = Sparse.eval value1338 (momentVector H) := by
  have heq : pivotMatrix1338 = (fun u v => node1338.transpose (pivotPermutation1338 u) v) := by apply Matrix.ext; unfold pivotMatrix1338 node1338 pivotPermutation1338; decide +kernel
  have hmoment : injectiveMoment H node1338 = injectiveMoment H pivotMatrix1338 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1338 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1338 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1338 (0 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1338 (0 : Fin 3) = raw9746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1338 raw9746; decide +kernel
    rw [heq]
    exact (canonical9746 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1338 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1338 (1 : Fin 3) = raw10148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1338 raw10148; decide +kernel
    rw [heq]
    exact (canonical10148 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1338 (2 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1338 (2 : Fin 3) = raw10157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1338 raw10157; decide +kernel
    rw [heq]
    exact (canonical10157 hH).trans (sound218 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1338 + (injectiveMoment H (mergeFirst pivotMatrix1338 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1338 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1338 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1338, value218, value219, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1339 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1339 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-1, -2, 2, 1], ![1, 3, -3, -1]]

theorem sound1339 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1339 = Sparse.eval value1339 (momentVector H) := by
  have heq : pivotMatrix1339 = (fun u v => node1339.transpose (pivotPermutation1339 u) v) := by apply Matrix.ext; unfold pivotMatrix1339 node1339 pivotPermutation1339; decide +kernel
  have hmoment : injectiveMoment H node1339 = injectiveMoment H pivotMatrix1339 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1339 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1339 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1339 (0 : Fin 3)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1339 (0 : Fin 3) = raw8808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1339 raw8808; decide +kernel
    rw [heq]
    exact (canonical8808 hH).trans (sound267 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1339 (1 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1339 (1 : Fin 3) = raw10122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1339 raw10122; decide +kernel
    rw [heq]
    exact (canonical10122 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1339 (2 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1339 (2 : Fin 3) = raw10127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1339 raw10127; decide +kernel
    rw [heq]
    exact (canonical10127 hH).trans (sound259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1339 + (injectiveMoment H (mergeFirst pivotMatrix1339 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1339 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1339 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1339, value259, value260, value267, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1340 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1340 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4]]

theorem sound1340 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1340 = Sparse.eval value1340 (momentVector H) := by
  have heq : pivotMatrix1340 = (fun u v => node1340 (pivotPermutation1340 u) v) := by apply Matrix.ext; unfold pivotMatrix1340 node1340 pivotPermutation1340; decide +kernel
  have hmoment : injectiveMoment H node1340 = injectiveMoment H pivotMatrix1340 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1340 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1340 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1340 (0 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1340 (0 : Fin 3) = raw9204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1340 raw9204; decide +kernel
    rw [heq]
    exact (canonical9204 hH).trans (sound51 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1340 (1 : Fin 3)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1340 (1 : Fin 3) = raw7873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1340 raw7873; decide +kernel
    rw [heq]
    exact (canonical7873 hH).trans (sound245 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1340 (2 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1340 (2 : Fin 3) = raw7837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1340 raw7837; decide +kernel
    rw [heq]
    exact (canonical7837 hH).trans (sound243 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1340 + (injectiveMoment H (mergeFirst pivotMatrix1340 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1340 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1340 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1340, value243, value245, value51, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1341 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1341 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-1, -1, 3, -1], ![1, 2, -4, 1]]

theorem sound1341 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1341 = Sparse.eval value1341 (momentVector H) := by
  have heq : pivotMatrix1341 = (fun u v => node1341.transpose (pivotPermutation1341 u) v) := by apply Matrix.ext; unfold pivotMatrix1341 node1341 pivotPermutation1341; decide +kernel
  have hmoment : injectiveMoment H node1341 = injectiveMoment H pivotMatrix1341 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1341 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1341 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1341 (0 : Fin 3)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1341 (0 : Fin 3) = raw8810 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1341 raw8810; decide +kernel
    rw [heq]
    exact (canonical8810 hH).trans (sound253 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1341 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1341 (1 : Fin 3) = raw10125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1341 raw10125; decide +kernel
    rw [heq]
    exact (canonical10125 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1341 (2 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1341 (2 : Fin 3) = raw10128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1341 raw10128; decide +kernel
    rw [heq]
    exact (canonical10128 hH).trans (sound244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1341 + (injectiveMoment H (mergeFirst pivotMatrix1341 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1341 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1341 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1341, value244, value246, value253, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1342 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1342 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -3, 1, 3], ![1, 3, -2, -2]]

theorem sound1342 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1342 = Sparse.eval value1342 (momentVector H) := by
  have heq : pivotMatrix1342 = (fun u v => node1342.transpose (pivotPermutation1342 u) v) := by apply Matrix.ext; unfold pivotMatrix1342 node1342 pivotPermutation1342; decide +kernel
  have hmoment : injectiveMoment H node1342 = injectiveMoment H pivotMatrix1342 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1342 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1342 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1342 (0 : Fin 3)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1342 (0 : Fin 3) = raw9747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1342 raw9747; decide +kernel
    rw [heq]
    exact (canonical9747 hH).trans (sound273 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1342 (1 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1342 (1 : Fin 3) = raw10149 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1342 raw10149; decide +kernel
    rw [heq]
    exact (canonical10149 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1342 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1342 (2 : Fin 3) = raw10158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1342 raw10158; decide +kernel
    rw [heq]
    exact (canonical10158 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1342 + (injectiveMoment H (mergeFirst pivotMatrix1342 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1342 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1342 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1342, value154, value187, value273, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1343 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -3, 3, 1], ![1, 3, -4, 0]]

theorem sound1343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1343 = Sparse.eval value1343 (momentVector H) := by
  have heq : pivotMatrix1343 = (fun u v => node1343.transpose (pivotPermutation1343 u) v) := by apply Matrix.ext; unfold pivotMatrix1343 node1343 pivotPermutation1343; decide +kernel
  have hmoment : injectiveMoment H node1343 = injectiveMoment H pivotMatrix1343 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1343 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1343 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1343 (0 : Fin 3)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1343 (0 : Fin 3) = raw9748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1343 raw9748; decide +kernel
    rw [heq]
    exact (canonical9748 hH).trans (sound255 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1343 (1 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1343 (1 : Fin 3) = raw10150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1343 raw10150; decide +kernel
    rw [heq]
    exact (canonical10150 hH).trans (sound213 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1343 (2 : Fin 3)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1343 (2 : Fin 3) = raw10159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1343 raw10159; decide +kernel
    rw [heq]
    exact (canonical10159 hH).trans (sound221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1343 + (injectiveMoment H (mergeFirst pivotMatrix1343 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1343 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1343 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1343, value213, value221, value255, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
