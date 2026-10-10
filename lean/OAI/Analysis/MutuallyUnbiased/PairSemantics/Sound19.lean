import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical278
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical311
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1216 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1216 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem sound1216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1216 = Sparse.eval value1216 (momentVector H) := by
  have heq : pivotMatrix1216 = (fun u v => node1216 (pivotPermutation1216 u) v) := by apply Matrix.ext; unfold pivotMatrix1216 node1216 pivotPermutation1216; decide +kernel
  have hmoment : injectiveMoment H node1216 = injectiveMoment H pivotMatrix1216 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1216 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1216 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1216 (0 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1216 (0 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1216 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1216 (1 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1216 (1 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1216 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1216 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1216 (2 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1216 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1216 + (injectiveMoment H (mergeFirst pivotMatrix1216 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1216 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1216 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1216, value149, value181, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1217 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1217 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem sound1217 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1217 = Sparse.eval value1217 (momentVector H) := by
  have heq : pivotMatrix1217 = (fun u v => node1217 (pivotPermutation1217 u) v) := by apply Matrix.ext; unfold pivotMatrix1217 node1217 pivotPermutation1217; decide +kernel
  have hmoment : injectiveMoment H node1217 = injectiveMoment H pivotMatrix1217 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1217 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1217 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1217 (0 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1217 (0 : Fin 3) = raw7035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1217 raw7035; decide +kernel
    rw [heq]
    exact (canonical7035 hH).trans (sound243 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1217 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1217 (1 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1217 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1217 (2 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1217 (2 : Fin 3) = raw7120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1217 raw7120; decide +kernel
    rw [heq]
    exact (canonical7120 hH).trans (sound292 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1217 + (injectiveMoment H (mergeFirst pivotMatrix1217 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1217 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1217 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1217, value181, value243, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1218 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1218 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -2, 3], ![0, 1, -2, 1], ![1, -1, 3, -3]]

theorem sound1218 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1218 = Sparse.eval value1218 (momentVector H) := by
  have heq : pivotMatrix1218 = (fun u v => node1218 (pivotPermutation1218 u) v) := by apply Matrix.ext; unfold pivotMatrix1218 node1218 pivotPermutation1218; decide +kernel
  have hmoment : injectiveMoment H node1218 = injectiveMoment H pivotMatrix1218 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1218 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1218 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1218 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1218 (0 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1218 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1218 (1 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1218 (1 : Fin 3) = raw7114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1218 raw7114; decide +kernel
    rw [heq]
    exact (canonical7114 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1218 (2 : Fin 3)) =
      Sparse.eval value143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1218 (2 : Fin 3) = raw7110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1218 raw7110; decide +kernel
    rw [heq]
    exact (canonical7110 hH).trans (sound143 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1218 + (injectiveMoment H (mergeFirst pivotMatrix1218 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1218 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1218 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1218, value143, value174, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1219 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 2, -2, 2], ![3, -2, 1, -2]]

theorem sound1219 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1219 = Sparse.eval value1219 (momentVector H) := by
  have heq : pivotMatrix1219 = (fun u v => node1219.transpose (pivotPermutation1219 u) v) := by apply Matrix.ext; unfold pivotMatrix1219 node1219 pivotPermutation1219; decide +kernel
  have hmoment : injectiveMoment H node1219 = injectiveMoment H pivotMatrix1219 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1219 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1219 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1219 (0 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1219 (0 : Fin 3) = raw7468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1219 raw7468; decide +kernel
    rw [heq]
    exact (canonical7468 hH).trans (sound274 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1219 (1 : Fin 3)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1219 (1 : Fin 3) = raw9738 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1219 raw9738; decide +kernel
    rw [heq]
    exact (canonical9738 hH).trans (sound265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1219 (2 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1219 (2 : Fin 3) = raw9743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1219 raw9743; decide +kernel
    rw [heq]
    exact (canonical9743 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1219 + (injectiveMoment H (mergeFirst pivotMatrix1219 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1219 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1219 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1219, value265, value274, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1220 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1220 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem sound1220 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1220 = Sparse.eval value1220 (momentVector H) := by
  have heq : pivotMatrix1220 = (fun u v => node1220 (pivotPermutation1220 u) v) := by apply Matrix.ext; unfold pivotMatrix1220 node1220 pivotPermutation1220; decide +kernel
  have hmoment : injectiveMoment H node1220 = injectiveMoment H pivotMatrix1220 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1220 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1220 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1220 (0 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1220 (0 : Fin 3) = raw7783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1220 raw7783; decide +kernel
    rw [heq]
    exact (canonical7783 hH).trans (sound168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1220 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1220 (1 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1220 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1220 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1220 (2 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1220 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1220 + (injectiveMoment H (mergeFirst pivotMatrix1220 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1220 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1220 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1220, value168, value181, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1221 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1221 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0]]

theorem sound1221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1221 = Sparse.eval value1221 (momentVector H) := by
  have heq : pivotMatrix1221 = (fun u v => node1221 (pivotPermutation1221 u) v) := by apply Matrix.ext; unfold pivotMatrix1221 node1221 pivotPermutation1221; decide +kernel
  have hmoment : injectiveMoment H node1221 = injectiveMoment H pivotMatrix1221 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1221 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1221 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1221 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1221 (0 : Fin 3) = raw7824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1221 raw7824; decide +kernel
    rw [heq]
    exact (canonical7824 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1221 (1 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1221 (1 : Fin 3) = raw7120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1221 raw7120; decide +kernel
    rw [heq]
    exact (canonical7120 hH).trans (sound292 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1221 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1221 (2 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1221 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1221 + (injectiveMoment H (mergeFirst pivotMatrix1221 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1221 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1221 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1221, value291, value292, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1222 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 2, 1, -1], ![3, -2, -2, 1]]

theorem sound1222 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1222 = Sparse.eval value1222 (momentVector H) := by
  have heq : pivotMatrix1222 = (fun u v => node1222.transpose (pivotPermutation1222 u) v) := by apply Matrix.ext; unfold pivotMatrix1222 node1222 pivotPermutation1222; decide +kernel
  have hmoment : injectiveMoment H node1222 = injectiveMoment H pivotMatrix1222 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1222 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1222 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1222 (0 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1222 (0 : Fin 3) = raw7469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1222 raw7469; decide +kernel
    rw [heq]
    exact (canonical7469 hH).trans (sound268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1222 (1 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1222 (1 : Fin 3) = raw9739 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1222 raw9739; decide +kernel
    rw [heq]
    exact (canonical9739 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1222 (2 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1222 (2 : Fin 3) = raw9744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1222 raw9744; decide +kernel
    rw [heq]
    exact (canonical9744 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1222 + (injectiveMoment H (mergeFirst pivotMatrix1222 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1222 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1222 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1222, value268, value279, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1223 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 2, -1, 1], ![3, -2, -1, 0]]

theorem sound1223 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1223 = Sparse.eval value1223 (momentVector H) := by
  have heq : pivotMatrix1223 = (fun u v => node1223.transpose (pivotPermutation1223 u) v) := by apply Matrix.ext; unfold pivotMatrix1223 node1223 pivotPermutation1223; decide +kernel
  have hmoment : injectiveMoment H node1223 = injectiveMoment H pivotMatrix1223 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1223 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1223 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1223 (0 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1223 (0 : Fin 3) = raw7523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1223 raw7523; decide +kernel
    rw [heq]
    exact (canonical7523 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1223 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1223 (1 : Fin 3) = raw9956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1223 raw9956; decide +kernel
    rw [heq]
    exact (canonical9956 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1223 (2 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1223 (2 : Fin 3) = raw9966 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1223 raw9966; decide +kernel
    rw [heq]
    exact (canonical9966 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1223 + (injectiveMoment H (mergeFirst pivotMatrix1223 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1223 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1223 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1223, value198, value224, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1224 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 3, -2, 1], ![3, -3, 1, -1]]

theorem sound1224 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1224 = Sparse.eval value1224 (momentVector H) := by
  have heq : pivotMatrix1224 = (fun u v => node1224.transpose (pivotPermutation1224 u) v) := by apply Matrix.ext; unfold pivotMatrix1224 node1224 pivotPermutation1224; decide +kernel
  have hmoment : injectiveMoment H node1224 = injectiveMoment H pivotMatrix1224 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1224 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1224 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1224 (0 : Fin 3)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1224 (0 : Fin 3) = raw7470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1224 raw7470; decide +kernel
    rw [heq]
    exact (canonical7470 hH).trans (sound273 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1224 (1 : Fin 3)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1224 (1 : Fin 3) = raw9740 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1224 raw9740; decide +kernel
    rw [heq]
    exact (canonical9740 hH).trans (sound277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1224 (2 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1224 (2 : Fin 3) = raw9745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1224 raw9745; decide +kernel
    rw [heq]
    exact (canonical9745 hH).trans (sound280 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1224 + (injectiveMoment H (mergeFirst pivotMatrix1224 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1224 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1224 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1224, value273, value277, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1225 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1225 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem sound1225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1225 = Sparse.eval value1225 (momentVector H) := by
  have heq : pivotMatrix1225 = (fun u v => node1225 (pivotPermutation1225 u) v) := by apply Matrix.ext; unfold pivotMatrix1225 node1225 pivotPermutation1225; decide +kernel
  have hmoment : injectiveMoment H node1225 = injectiveMoment H pivotMatrix1225 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1225 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1225 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1225 (0 : Fin 3)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1225 (0 : Fin 3) = raw7784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1225 raw7784; decide +kernel
    rw [heq]
    exact (canonical7784 hH).trans (sound289 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1225 (1 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1225 (1 : Fin 3) = raw7120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1225 raw7120; decide +kernel
    rw [heq]
    exact (canonical7120 hH).trans (sound292 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1225 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1225 (2 : Fin 3) = raw7108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1225 raw7108; decide +kernel
    rw [heq]
    exact (canonical7108 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1225 + (injectiveMoment H (mergeFirst pivotMatrix1225 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1225 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1225 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1225, value289, value292, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1226 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 3, -1, 0], ![3, -3, -1, 1]]

theorem sound1226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1226 = Sparse.eval value1226 (momentVector H) := by
  have heq : pivotMatrix1226 = (fun u v => node1226.transpose (pivotPermutation1226 u) v) := by apply Matrix.ext; unfold pivotMatrix1226 node1226 pivotPermutation1226; decide +kernel
  have hmoment : injectiveMoment H node1226 = injectiveMoment H pivotMatrix1226 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1226 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1226 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1226 (0 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1226 (0 : Fin 3) = raw7525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1226 raw7525; decide +kernel
    rw [heq]
    exact (canonical7525 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1226 (1 : Fin 3)) =
      Sparse.eval value220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1226 (1 : Fin 3) = raw9958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1226 raw9958; decide +kernel
    rw [heq]
    exact (canonical9958 hH).trans (sound220 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1226 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1226 (2 : Fin 3) = raw9969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1226 raw9969; decide +kernel
    rw [heq]
    exact (canonical9969 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1226 + (injectiveMoment H (mergeFirst pivotMatrix1226 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1226 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1226 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1226, value198, value220, value222, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1227 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1227 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

theorem sound1227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1227 = Sparse.eval value1227 (momentVector H) := by
  have heq : pivotMatrix1227 = (fun u v => node1227 (pivotPermutation1227 u) v) := by apply Matrix.ext; unfold pivotMatrix1227 node1227 pivotPermutation1227; decide +kernel
  have hmoment : injectiveMoment H node1227 = injectiveMoment H pivotMatrix1227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1227 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1227 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1227 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1227 (0 : Fin 3) = raw8302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1227 raw8302; decide +kernel
    rw [heq]
    exact (canonical8302 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1227 (1 : Fin 3)) =
      Sparse.eval value143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1227 (1 : Fin 3) = raw7130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1227 raw7130; decide +kernel
    rw [heq]
    exact (canonical7130 hH).trans (sound143 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1227 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1227 (2 : Fin 3) = raw7109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1227 raw7109; decide +kernel
    rw [heq]
    exact (canonical7109 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1227 + (injectiveMoment H (mergeFirst pivotMatrix1227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1227, value143, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1228 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1228 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 0, 4, -4], ![1, -1, -1, 1]]

theorem sound1228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1228 = Sparse.eval value1228 (momentVector H) := by
  have heq : pivotMatrix1228 = (fun u v => node1228 (pivotPermutation1228 u) v) := by apply Matrix.ext; unfold pivotMatrix1228 node1228 pivotPermutation1228; decide +kernel
  have hmoment : injectiveMoment H node1228 = injectiveMoment H pivotMatrix1228 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1228 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1228 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1228 (0 : Fin 3)) =
      Sparse.eval value242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1228 (0 : Fin 3) = raw7785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1228 raw7785; decide +kernel
    rw [heq]
    exact (canonical7785 hH).trans (sound242 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1228 (1 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1228 (1 : Fin 3) = raw7121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1228 raw7121; decide +kernel
    rw [heq]
    exact (canonical7121 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1228 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1228 (2 : Fin 3) = raw7109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1228 raw7109; decide +kernel
    rw [heq]
    exact (canonical7109 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1228 + (injectiveMoment H (mergeFirst pivotMatrix1228 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1228 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1228 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1228, value242, value243, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1229 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 4, -2, 0], ![3, -4, 0, 1]]

theorem sound1229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1229 = Sparse.eval value1229 (momentVector H) := by
  have heq : pivotMatrix1229 = (fun u v => node1229.transpose (pivotPermutation1229 u) v) := by apply Matrix.ext; unfold pivotMatrix1229 node1229 pivotPermutation1229; decide +kernel
  have hmoment : injectiveMoment H node1229 = injectiveMoment H pivotMatrix1229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1229 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1229 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1229 (0 : Fin 3)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1229 (0 : Fin 3) = raw7526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1229 raw7526; decide +kernel
    rw [heq]
    exact (canonical7526 hH).trans (sound217 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1229 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1229 (1 : Fin 3) = raw9960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1229 raw9960; decide +kernel
    rw [heq]
    exact (canonical9960 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1229 (2 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1229 (2 : Fin 3) = raw9972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1229 raw9972; decide +kernel
    rw [heq]
    exact (canonical9972 hH).trans (sound199 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1229 + (injectiveMoment H (mergeFirst pivotMatrix1229 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1229 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1229 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1229, value193, value199, value217, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1230 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-2, -2, 3, 1], ![3, 1, -4, 0]]

theorem sound1230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1230 = Sparse.eval value1230 (momentVector H) := by
  have heq : pivotMatrix1230 = (fun u v => node1230.transpose (pivotPermutation1230 u) v) := by apply Matrix.ext; unfold pivotMatrix1230 node1230 pivotPermutation1230; decide +kernel
  have hmoment : injectiveMoment H node1230 = injectiveMoment H pivotMatrix1230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1230 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1230 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1230 (0 : Fin 3)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1230 (0 : Fin 3) = raw7906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1230 raw7906; decide +kernel
    rw [heq]
    exact (canonical7906 hH).trans (sound245 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1230 (1 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1230 (1 : Fin 3) = raw10092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1230 raw10092; decide +kernel
    rw [heq]
    exact (canonical10092 hH).trans (sound213 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1230 (2 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1230 (2 : Fin 3) = raw10099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1230 raw10099; decide +kernel
    rw [heq]
    exact (canonical10099 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1230 + (injectiveMoment H (mergeFirst pivotMatrix1230 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1230 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1230 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1230, value213, value225, value245, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1231 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1231 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem sound1231 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1231 = Sparse.eval value1231 (momentVector H) := by
  have heq : pivotMatrix1231 = (fun u v => node1231 (pivotPermutation1231 u) v) := by apply Matrix.ext; unfold pivotMatrix1231 node1231 pivotPermutation1231; decide +kernel
  have hmoment : injectiveMoment H node1231 = injectiveMoment H pivotMatrix1231 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1231 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1231 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1231 (0 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1231 (0 : Fin 3) = raw7787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1231 raw7787; decide +kernel
    rw [heq]
    exact (canonical7787 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1231 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1231 (1 : Fin 3) = raw7123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1231 raw7123; decide +kernel
    rw [heq]
    exact (canonical7123 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1231 (2 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1231 (2 : Fin 3) = raw7120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1231 raw7120; decide +kernel
    rw [heq]
    exact (canonical7120 hH).trans (sound292 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1231 + (injectiveMoment H (mergeFirst pivotMatrix1231 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1231 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1231 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1231, value215, value222, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1232 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1232 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -2, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem sound1232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1232 = Sparse.eval value1232 (momentVector H) := by
  have heq : pivotMatrix1232 = (fun u v => node1232 (pivotPermutation1232 u) v) := by apply Matrix.ext; unfold pivotMatrix1232 node1232 pivotPermutation1232; decide +kernel
  have hmoment : injectiveMoment H node1232 = injectiveMoment H pivotMatrix1232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1232 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1232 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1232 (0 : Fin 3)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1232 (0 : Fin 3) = raw7788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1232 raw7788; decide +kernel
    rw [heq]
    exact (canonical7788 hH).trans (sound221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1232 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1232 (1 : Fin 3) = raw7124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1232 raw7124; decide +kernel
    rw [heq]
    exact (canonical7124 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1232 (2 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1232 (2 : Fin 3) = raw7121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1232 raw7121; decide +kernel
    rw [heq]
    exact (canonical7121 hH).trans (sound243 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1232 + (injectiveMoment H (mergeFirst pivotMatrix1232 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1232 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1232 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1232, value201, value221, value243, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1233 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-1, 0, 3, -2], ![2, 2, -5, 1]]

theorem sound1233 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1233 = Sparse.eval value1233 (momentVector H) := by
  have heq : pivotMatrix1233 = (fun u v => node1233.transpose (pivotPermutation1233 u) v) := by apply Matrix.ext; unfold pivotMatrix1233 node1233 pivotPermutation1233; decide +kernel
  have hmoment : injectiveMoment H node1233 = injectiveMoment H pivotMatrix1233 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1233 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1233 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1233 (0 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1233 (0 : Fin 3) = raw5817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1233 raw5817; decide +kernel
    rw [heq]
    exact (canonical5817 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1233 (1 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1233 (1 : Fin 3) = raw8232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1233 raw8232; decide +kernel
    rw [heq]
    exact (canonical8232 hH).trans (sound120 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1233 (2 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1233 (2 : Fin 3) = raw8244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1233 raw8244; decide +kernel
    rw [heq]
    exact (canonical8244 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1233 + (injectiveMoment H (mergeFirst pivotMatrix1233 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1233 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1233 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1233, value120, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1234 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-1, 1, 2, -2], ![2, 1, -4, 1]]

theorem sound1234 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1234 = Sparse.eval value1234 (momentVector H) := by
  have heq : pivotMatrix1234 = (fun u v => node1234.transpose (pivotPermutation1234 u) v) := by apply Matrix.ext; unfold pivotMatrix1234 node1234 pivotPermutation1234; decide +kernel
  have hmoment : injectiveMoment H node1234 = injectiveMoment H pivotMatrix1234 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1234 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1234 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1234 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1234 (0 : Fin 3) = raw5818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1234 raw5818; decide +kernel
    rw [heq]
    exact (canonical5818 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1234 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1234 (1 : Fin 3) = raw8234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1234 raw8234; decide +kernel
    rw [heq]
    exact (canonical8234 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1234 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1234 (2 : Fin 3) = raw8245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1234 raw8245; decide +kernel
    rw [heq]
    exact (canonical8245 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1234 + (injectiveMoment H (mergeFirst pivotMatrix1234 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1234 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1234 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1234, value134, value146, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1235 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-1, 2, 1, -2], ![2, 0, -3, 1]]

theorem sound1235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1235 = Sparse.eval value1235 (momentVector H) := by
  have heq : pivotMatrix1235 = (fun u v => node1235.transpose (pivotPermutation1235 u) v) := by apply Matrix.ext; unfold pivotMatrix1235 node1235 pivotPermutation1235; decide +kernel
  have hmoment : injectiveMoment H node1235 = injectiveMoment H pivotMatrix1235 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1235 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1235 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1235 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1235 (0 : Fin 3) = raw5819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1235 raw5819; decide +kernel
    rw [heq]
    exact (canonical5819 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1235 (1 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1235 (1 : Fin 3) = raw8236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1235 raw8236; decide +kernel
    rw [heq]
    exact (canonical8236 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1235 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1235 (2 : Fin 3) = raw8246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1235 raw8246; decide +kernel
    rw [heq]
    exact (canonical8246 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1235 + (injectiveMoment H (mergeFirst pivotMatrix1235 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1235 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1235 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1235, value111, value177, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1236 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -2, 2, 1], ![2, 3, -4, -1]]

theorem sound1236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1236 = Sparse.eval value1236 (momentVector H) := by
  have heq : pivotMatrix1236 = (fun u v => node1236.transpose (pivotPermutation1236 u) v) := by apply Matrix.ext; unfold pivotMatrix1236 node1236 pivotPermutation1236; decide +kernel
  have hmoment : injectiveMoment H node1236 = injectiveMoment H pivotMatrix1236 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1236 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1236 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1236 (0 : Fin 3)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1236 (0 : Fin 3) = raw6901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1236 raw6901; decide +kernel
    rw [heq]
    exact (canonical6901 hH).trans (sound144 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1236 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1236 (1 : Fin 3) = raw8891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1236 raw8891; decide +kernel
    rw [heq]
    exact (canonical8891 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1236 (2 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1236 (2 : Fin 3) = raw8901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1236 raw8901; decide +kernel
    rw [heq]
    exact (canonical8901 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1236 + (injectiveMoment H (mergeFirst pivotMatrix1236 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1236 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1236 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1236, value144, value149, value152, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1237 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-1, -1, 1, 1], ![2, 2, -2, -2]]

theorem sound1237 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1237 = Sparse.eval value1237 (momentVector H) := by
  have heq : pivotMatrix1237 = (fun u v => node1237.transpose (pivotPermutation1237 u) v) := by apply Matrix.ext; unfold pivotMatrix1237 node1237 pivotPermutation1237; decide +kernel
  have hmoment : injectiveMoment H node1237 = injectiveMoment H pivotMatrix1237 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1237 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1237 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1237 (0 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1237 (0 : Fin 3) = raw6586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1237 raw6586; decide +kernel
    rw [heq]
    exact (canonical6586 hH).trans (sound275 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1237 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1237 (1 : Fin 3) = raw8802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1237 raw8802; decide +kernel
    rw [heq]
    exact (canonical8802 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1237 (2 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1237 (2 : Fin 3) = raw8809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1237 raw8809; decide +kernel
    rw [heq]
    exact (canonical8809 hH).trans (sound283 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1237 + (injectiveMoment H (mergeFirst pivotMatrix1237 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1237 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1237 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1237, value275, value279, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1238 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -1, -2, 4], ![2, 2, 0, -4]]

theorem sound1238 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1238 = Sparse.eval value1238 (momentVector H) := by
  have heq : pivotMatrix1238 = (fun u v => node1238.transpose (pivotPermutation1238 u) v) := by apply Matrix.ext; unfold pivotMatrix1238 node1238 pivotPermutation1238; decide +kernel
  have hmoment : injectiveMoment H node1238 = injectiveMoment H pivotMatrix1238 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1238 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1238 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1238 (0 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1238 (0 : Fin 3) = raw6902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1238 raw6902; decide +kernel
    rw [heq]
    exact (canonical6902 hH).trans (sound218 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1238 (1 : Fin 3)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1238 (1 : Fin 3) = raw8892 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1238 raw8892; decide +kernel
    rw [heq]
    exact (canonical8892 hH).trans (sound200 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1238 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1238 (2 : Fin 3) = raw8902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1238 raw8902; decide +kernel
    rw [heq]
    exact (canonical8902 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1238 + (injectiveMoment H (mergeFirst pivotMatrix1238 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1238 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1238 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1238, value200, value206, value218, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1239 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -1, -1, 3], ![2, 2, -1, -3]]

theorem sound1239 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1239 = Sparse.eval value1239 (momentVector H) := by
  have heq : pivotMatrix1239 = (fun u v => node1239.transpose (pivotPermutation1239 u) v) := by apply Matrix.ext; unfold pivotMatrix1239 node1239 pivotPermutation1239; decide +kernel
  have hmoment : injectiveMoment H node1239 = injectiveMoment H pivotMatrix1239 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1239 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1239 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1239 (0 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1239 (0 : Fin 3) = raw6903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1239 raw6903; decide +kernel
    rw [heq]
    exact (canonical6903 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1239 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1239 (1 : Fin 3) = raw8893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1239 raw8893; decide +kernel
    rw [heq]
    exact (canonical8893 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1239 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1239 (2 : Fin 3) = raw8903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1239 raw8903; decide +kernel
    rw [heq]
    exact (canonical8903 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1239 + (injectiveMoment H (mergeFirst pivotMatrix1239 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1239 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1239 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1239, value223, value225, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1240 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1240 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, -1, 3, -1], ![2, 2, -5, 1]]

theorem sound1240 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1240 = Sparse.eval value1240 (momentVector H) := by
  have heq : pivotMatrix1240 = (fun u v => node1240.transpose (pivotPermutation1240 u) v) := by apply Matrix.ext; unfold pivotMatrix1240 node1240 pivotPermutation1240; decide +kernel
  have hmoment : injectiveMoment H node1240 = injectiveMoment H pivotMatrix1240 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1240 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1240 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1240 (0 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1240 (0 : Fin 3) = raw6904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1240 raw6904; decide +kernel
    rw [heq]
    exact (canonical6904 hH).trans (sound124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1240 (1 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1240 (1 : Fin 3) = raw8895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1240 raw8895; decide +kernel
    rw [heq]
    exact (canonical8895 hH).trans (sound127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1240 (2 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1240 (2 : Fin 3) = raw8904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1240 raw8904; decide +kernel
    rw [heq]
    exact (canonical8904 hH).trans (sound124 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1240 + (injectiveMoment H (mergeFirst pivotMatrix1240 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1240 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1240 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1240, value124, value127, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1241 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1241 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem sound1241 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1241 = Sparse.eval value1241 (momentVector H) := by
  have heq : pivotMatrix1241 = (fun u v => node1241 (pivotPermutation1241 u) v) := by apply Matrix.ext; unfold pivotMatrix1241 node1241 pivotPermutation1241; decide +kernel
  have hmoment : injectiveMoment H node1241 = injectiveMoment H pivotMatrix1241 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1241 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1241 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1241 (0 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1241 (0 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1241 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1241 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1241 (1 : Fin 3) = raw7206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1241 raw7206; decide +kernel
    rw [heq]
    exact (canonical7206 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1241 (2 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1241 (2 : Fin 3) = raw7241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1241 raw7241; decide +kernel
    rw [heq]
    exact (canonical7241 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1241 + (injectiveMoment H (mergeFirst pivotMatrix1241 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1241 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1241 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1241, value11, value284, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1242 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1242 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound1242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1242 = Sparse.eval value1242 (momentVector H) := by
  have heq : pivotMatrix1242 = (fun u v => node1242 (pivotPermutation1242 u) v) := by apply Matrix.ext; unfold pivotMatrix1242 node1242 pivotPermutation1242; decide +kernel
  have hmoment : injectiveMoment H node1242 = injectiveMoment H pivotMatrix1242 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1242 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1242 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1242 (0 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1242 (0 : Fin 3) = raw6546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1242 raw6546; decide +kernel
    rw [heq]
    exact (canonical6546 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1242 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1242 (1 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1242 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1242 (2 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1242 (2 : Fin 3) = raw7243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1242 raw7243; decide +kernel
    rw [heq]
    exact (canonical7243 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1242 + (injectiveMoment H (mergeFirst pivotMatrix1242 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1242 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1242 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1242, value294, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1243 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1243 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

theorem sound1243 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1243 = Sparse.eval value1243 (momentVector H) := by
  have heq : pivotMatrix1243 = (fun u v => node1243 (pivotPermutation1243 u) v) := by apply Matrix.ext; unfold pivotMatrix1243 node1243 pivotPermutation1243; decide +kernel
  have hmoment : injectiveMoment H node1243 = injectiveMoment H pivotMatrix1243 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1243 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1243 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1243 (0 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1243 (0 : Fin 3) = raw6560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1243 raw6560; decide +kernel
    rw [heq]
    exact (canonical6560 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1243 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1243 (1 : Fin 3) = raw7246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1243 raw7246; decide +kernel
    rw [heq]
    exact (canonical7246 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1243 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1243 (2 : Fin 3) = raw7248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1243 raw7248; decide +kernel
    rw [heq]
    exact (canonical7248 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1243 + (injectiveMoment H (mergeFirst pivotMatrix1243 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1243 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1243 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1243, value149, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1244 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-1, 2, -2, 1], ![2, -1, 1, -2]]

theorem sound1244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1244 = Sparse.eval value1244 (momentVector H) := by
  have heq : pivotMatrix1244 = (fun u v => node1244.transpose (pivotPermutation1244 u) v) := by apply Matrix.ext; unfold pivotMatrix1244 node1244 pivotPermutation1244; decide +kernel
  have hmoment : injectiveMoment H node1244 = injectiveMoment H pivotMatrix1244 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1244 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1244 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1244 (0 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1244 (0 : Fin 3) = raw6591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1244 raw6591; decide +kernel
    rw [heq]
    exact (canonical6591 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1244 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1244 (1 : Fin 3) = raw8804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1244 raw8804; decide +kernel
    rw [heq]
    exact (canonical8804 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1244 (2 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1244 (2 : Fin 3) = raw8820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1244 raw8820; decide +kernel
    rw [heq]
    exact (canonical8820 hH).trans (sound283 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1244 + (injectiveMoment H (mergeFirst pivotMatrix1244 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1244 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1244 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1244, value276, value279, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1245 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1245 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1]]

theorem sound1245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1245 = Sparse.eval value1245 (momentVector H) := by
  have heq : pivotMatrix1245 = (fun u v => node1245 (pivotPermutation1245 u) v) := by apply Matrix.ext; unfold pivotMatrix1245 node1245 pivotPermutation1245; decide +kernel
  have hmoment : injectiveMoment H node1245 = injectiveMoment H pivotMatrix1245 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1245 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1245 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1245 (0 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1245 (0 : Fin 3) = raw7814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1245 raw7814; decide +kernel
    rw [heq]
    exact (canonical7814 hH).trans (sound284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1245 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1245 (1 : Fin 3) = raw7213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1245 raw7213; decide +kernel
    rw [heq]
    exact (canonical7213 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1245 (2 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1245 (2 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1245 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1245 + (injectiveMoment H (mergeFirst pivotMatrix1245 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1245 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1245 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1245, value230, value284, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1246 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1246 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 0, -1, 0]]

theorem sound1246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1246 = Sparse.eval value1246 (momentVector H) := by
  have heq : pivotMatrix1246 = (fun u v => node1246 (pivotPermutation1246 u) v) := by apply Matrix.ext; unfold pivotMatrix1246 node1246 pivotPermutation1246; decide +kernel
  have hmoment : injectiveMoment H node1246 = injectiveMoment H pivotMatrix1246 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1246 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1246 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1246 (0 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1246 (0 : Fin 3) = raw7841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1246 raw7841; decide +kernel
    rw [heq]
    exact (canonical7841 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1246 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1246 (1 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1246 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1246 (2 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1246 (2 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1246 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1246 + (injectiveMoment H (mergeFirst pivotMatrix1246 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1246 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1246 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1246, value230, value287, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1247 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1247 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![2, -1, -2, 1]]

theorem sound1247 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1247 = Sparse.eval value1247 (momentVector H) := by
  have heq : pivotMatrix1247 = (fun u v => node1247.transpose (pivotPermutation1247 u) v) := by apply Matrix.ext; unfold pivotMatrix1247 node1247 pivotPermutation1247; decide +kernel
  have hmoment : injectiveMoment H node1247 = injectiveMoment H pivotMatrix1247 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1247 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1247 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1247 (0 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1247 (0 : Fin 3) = raw6592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1247 raw6592; decide +kernel
    rw [heq]
    exact (canonical6592 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1247 (1 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1247 (1 : Fin 3) = raw8805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1247 raw8805; decide +kernel
    rw [heq]
    exact (canonical8805 hH).trans (sound288 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1247 (2 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1247 (2 : Fin 3) = raw8821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1247 raw8821; decide +kernel
    rw [heq]
    exact (canonical8821 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1247 + (injectiveMoment H (mergeFirst pivotMatrix1247 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1247 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1247 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1247, value276, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1248 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 2, 1, -2], ![2, -1, -3, 2]]

theorem sound1248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1248 = Sparse.eval value1248 (momentVector H) := by
  have heq : pivotMatrix1248 = (fun u v => node1248.transpose (pivotPermutation1248 u) v) := by apply Matrix.ext; unfold pivotMatrix1248 node1248 pivotPermutation1248; decide +kernel
  have hmoment : injectiveMoment H node1248 = injectiveMoment H pivotMatrix1248 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1248 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1248 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1248 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1248 (0 : Fin 3) = raw6908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1248 raw6908; decide +kernel
    rw [heq]
    exact (canonical6908 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1248 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1248 (1 : Fin 3) = raw8897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1248 raw8897; decide +kernel
    rw [heq]
    exact (canonical8897 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1248 (2 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1248 (2 : Fin 3) = raw8910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1248 raw8910; decide +kernel
    rw [heq]
    exact (canonical8910 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1248 + (injectiveMoment H (mergeFirst pivotMatrix1248 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1248 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1248 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1248, value180, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1249 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 3, -1, -1], ![2, -2, -1, 1]]

theorem sound1249 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1249 = Sparse.eval value1249 (momentVector H) := by
  have heq : pivotMatrix1249 = (fun u v => node1249.transpose (pivotPermutation1249 u) v) := by apply Matrix.ext; unfold pivotMatrix1249 node1249 pivotPermutation1249; decide +kernel
  have hmoment : injectiveMoment H node1249 = injectiveMoment H pivotMatrix1249 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1249 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1249 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1249 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1249 (0 : Fin 3) = raw6910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1249 raw6910; decide +kernel
    rw [heq]
    exact (canonical6910 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1249 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1249 (1 : Fin 3) = raw8898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1249 raw8898; decide +kernel
    rw [heq]
    exact (canonical8898 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1249 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1249 (2 : Fin 3) = raw8911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1249 raw8911; decide +kernel
    rw [heq]
    exact (canonical8911 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1249 + (injectiveMoment H (mergeFirst pivotMatrix1249 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1249 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1249 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1249, value226, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1250 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 3, 0, -2], ![2, -2, -2, 2]]

theorem sound1250 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1250 = Sparse.eval value1250 (momentVector H) := by
  have heq : pivotMatrix1250 = (fun u v => node1250.transpose (pivotPermutation1250 u) v) := by apply Matrix.ext; unfold pivotMatrix1250 node1250 pivotPermutation1250; decide +kernel
  have hmoment : injectiveMoment H node1250 = injectiveMoment H pivotMatrix1250 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1250 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1250 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1250 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1250 (0 : Fin 3) = raw6911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1250 raw6911; decide +kernel
    rw [heq]
    exact (canonical6911 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1250 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1250 (1 : Fin 3) = raw8899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1250 raw8899; decide +kernel
    rw [heq]
    exact (canonical8899 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1250 (2 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1250 (2 : Fin 3) = raw8912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1250 raw8912; decide +kernel
    rw [heq]
    exact (canonical8912 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1250 + (injectiveMoment H (mergeFirst pivotMatrix1250 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1250 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1250 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1250, value209, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1251 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 4, -1, -2], ![2, -3, -1, 2]]

theorem sound1251 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1251 = Sparse.eval value1251 (momentVector H) := by
  have heq : pivotMatrix1251 = (fun u v => node1251.transpose (pivotPermutation1251 u) v) := by apply Matrix.ext; unfold pivotMatrix1251 node1251 pivotPermutation1251; decide +kernel
  have hmoment : injectiveMoment H node1251 = injectiveMoment H pivotMatrix1251 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1251 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1251 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1251 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1251 (0 : Fin 3) = raw6912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1251 raw6912; decide +kernel
    rw [heq]
    exact (canonical6912 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1251 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1251 (1 : Fin 3) = raw8900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1251 raw8900; decide +kernel
    rw [heq]
    exact (canonical8900 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1251 (2 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1251 (2 : Fin 3) = raw8913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1251 raw8913; decide +kernel
    rw [heq]
    exact (canonical8913 hH).trans (sound228 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1251 + (injectiveMoment H (mergeFirst pivotMatrix1251 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1251 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1251 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1251, value225, value228, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1252 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1252 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, 0, -2, 2], ![1, -1, 3, -3]]

theorem sound1252 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1252 = Sparse.eval value1252 (momentVector H) := by
  have heq : pivotMatrix1252 = (fun u v => node1252 (pivotPermutation1252 u) v) := by apply Matrix.ext; unfold pivotMatrix1252 node1252 pivotPermutation1252; decide +kernel
  have hmoment : injectiveMoment H node1252 = injectiveMoment H pivotMatrix1252 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1252 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1252 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1252 (0 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1252 (0 : Fin 3) = raw7848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1252 raw7848; decide +kernel
    rw [heq]
    exact (canonical7848 hH).trans (sound168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1252 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1252 (1 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1252 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1252 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1252 (2 : Fin 3) = raw7191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1252 raw7191; decide +kernel
    rw [heq]
    exact (canonical7191 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1252 + (injectiveMoment H (mergeFirst pivotMatrix1252 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1252 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1252 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1252, value168, value174, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1253 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, -2, 1, 2], ![2, 2, -2, -2]]

theorem sound1253 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1253 = Sparse.eval value1253 (momentVector H) := by
  have heq : pivotMatrix1253 = (fun u v => node1253.transpose (pivotPermutation1253 u) v) := by apply Matrix.ext; unfold pivotMatrix1253 node1253 pivotPermutation1253; decide +kernel
  have hmoment : injectiveMoment H node1253 = injectiveMoment H pivotMatrix1253 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1253 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1253 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1253 (0 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1253 (0 : Fin 3) = raw7473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1253 raw7473; decide +kernel
    rw [heq]
    exact (canonical7473 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1253 (1 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1253 (1 : Fin 3) = raw9742 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1253 raw9742; decide +kernel
    rw [heq]
    exact (canonical9742 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1253 (2 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1253 (2 : Fin 3) = raw9749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1253 raw9749; decide +kernel
    rw [heq]
    exact (canonical9749 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1253 + (injectiveMoment H (mergeFirst pivotMatrix1253 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1253 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1253 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1253, value274, value279, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1254 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, -1, 4], ![2, 2, -1, -3]]

theorem sound1254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1254 = Sparse.eval value1254 (momentVector H) := by
  have heq : pivotMatrix1254 = (fun u v => node1254.transpose (pivotPermutation1254 u) v) := by apply Matrix.ext; unfold pivotMatrix1254 node1254 pivotPermutation1254; decide +kernel
  have hmoment : injectiveMoment H node1254 = injectiveMoment H pivotMatrix1254 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1254 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1254 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1254 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1254 (0 : Fin 3) = raw7530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1254 raw7530; decide +kernel
    rw [heq]
    exact (canonical7530 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1254 (1 : Fin 3)) =
      Sparse.eval value125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1254 (1 : Fin 3) = raw9961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1254 raw9961; decide +kernel
    rw [heq]
    exact (canonical9961 hH).trans (sound125 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1254 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1254 (2 : Fin 3) = raw9973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1254 raw9973; decide +kernel
    rw [heq]
    exact (canonical9973 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1254 + (injectiveMoment H (mergeFirst pivotMatrix1254 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1254 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1254 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1254, value125, value146, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1255 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 0, 3], ![2, 2, -2, -2]]

theorem sound1255 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1255 = Sparse.eval value1255 (momentVector H) := by
  have heq : pivotMatrix1255 = (fun u v => node1255.transpose (pivotPermutation1255 u) v) := by apply Matrix.ext; unfold pivotMatrix1255 node1255 pivotPermutation1255; decide +kernel
  have hmoment : injectiveMoment H node1255 = injectiveMoment H pivotMatrix1255 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1255 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1255 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1255 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1255 (0 : Fin 3) = raw7531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1255 raw7531; decide +kernel
    rw [heq]
    exact (canonical7531 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1255 (1 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1255 (1 : Fin 3) = raw9962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1255 raw9962; decide +kernel
    rw [heq]
    exact (canonical9962 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1255 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1255 (2 : Fin 3) = raw9974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1255 raw9974; decide +kernel
    rw [heq]
    exact (canonical9974 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1255 + (injectiveMoment H (mergeFirst pivotMatrix1255 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1255 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1255 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1255, value151, value177, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1256 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 1, 2], ![2, 2, -3, -1]]

theorem sound1256 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1256 = Sparse.eval value1256 (momentVector H) := by
  have heq : pivotMatrix1256 = (fun u v => node1256.transpose (pivotPermutation1256 u) v) := by apply Matrix.ext; unfold pivotMatrix1256 node1256 pivotPermutation1256; decide +kernel
  have hmoment : injectiveMoment H node1256 = injectiveMoment H pivotMatrix1256 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1256 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1256 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1256 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1256 (0 : Fin 3) = raw7532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1256 raw7532; decide +kernel
    rw [heq]
    exact (canonical7532 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1256 (1 : Fin 3)) =
      Sparse.eval value182 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1256 (1 : Fin 3) = raw9963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1256 raw9963; decide +kernel
    rw [heq]
    exact (canonical9963 hH).trans (sound182 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1256 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1256 (2 : Fin 3) = raw9975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1256 raw9975; decide +kernel
    rw [heq]
    exact (canonical9975 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1256 + (injectiveMoment H (mergeFirst pivotMatrix1256 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1256 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1256 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1256, value177, value182, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1257 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 2, 1], ![2, 2, -4, 0]]

theorem sound1257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1257 = Sparse.eval value1257 (momentVector H) := by
  have heq : pivotMatrix1257 = (fun u v => node1257.transpose (pivotPermutation1257 u) v) := by apply Matrix.ext; unfold pivotMatrix1257 node1257 pivotPermutation1257; decide +kernel
  have hmoment : injectiveMoment H node1257 = injectiveMoment H pivotMatrix1257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1257 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1257 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1257 (0 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (0 : Fin 3) = raw7533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw7533; decide +kernel
    rw [heq]
    exact (canonical7533 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1257 (1 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (1 : Fin 3) = raw9964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw9964; decide +kernel
    rw [heq]
    exact (canonical9964 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1257 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (2 : Fin 3) = raw9976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw9976; decide +kernel
    rw [heq]
    exact (canonical9976 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1257 + (injectiveMoment H (mergeFirst pivotMatrix1257 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1257 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1257 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1257, value146, value151, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1258 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, -2, 3, 0], ![2, 2, -5, 1]]

theorem sound1258 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1258 = Sparse.eval value1258 (momentVector H) := by
  have heq : pivotMatrix1258 = (fun u v => node1258.transpose (pivotPermutation1258 u) v) := by apply Matrix.ext; unfold pivotMatrix1258 node1258 pivotPermutation1258; decide +kernel
  have hmoment : injectiveMoment H node1258 = injectiveMoment H pivotMatrix1258 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1258 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1258 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1258 (0 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1258 (0 : Fin 3) = raw7534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1258 raw7534; decide +kernel
    rw [heq]
    exact (canonical7534 hH).trans (sound127 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1258 (1 : Fin 3)) =
      Sparse.eval value125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1258 (1 : Fin 3) = raw9965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1258 raw9965; decide +kernel
    rw [heq]
    exact (canonical9965 hH).trans (sound125 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1258 (2 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1258 (2 : Fin 3) = raw9977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1258 raw9977; decide +kernel
    rw [heq]
    exact (canonical9977 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1258 + (injectiveMoment H (mergeFirst pivotMatrix1258 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1258 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1258 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1258, value120, value125, value127, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1259 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1259 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem sound1259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1259 = Sparse.eval value1259 (momentVector H) := by
  have heq : pivotMatrix1259 = (fun u v => node1259 (pivotPermutation1259 u) v) := by apply Matrix.ext; unfold pivotMatrix1259 node1259 pivotPermutation1259; decide +kernel
  have hmoment : injectiveMoment H node1259 = injectiveMoment H pivotMatrix1259 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1259 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1259 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1259 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1259 (0 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1259 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1259 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1259 (1 : Fin 3) = raw7241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1259 raw7241; decide +kernel
    rw [heq]
    exact (canonical7241 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1259 (2 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1259 (2 : Fin 3) = raw7242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1259 raw7242; decide +kernel
    rw [heq]
    exact (canonical7242 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1259 + (injectiveMoment H (mergeFirst pivotMatrix1259 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1259 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1259 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1259, value272, value284, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1260 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1260 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem sound1260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1260 = Sparse.eval value1260 (momentVector H) := by
  have heq : pivotMatrix1260 = (fun u v => node1260 (pivotPermutation1260 u) v) := by apply Matrix.ext; unfold pivotMatrix1260 node1260 pivotPermutation1260; decide +kernel
  have hmoment : injectiveMoment H node1260 = injectiveMoment H pivotMatrix1260 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1260 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1260 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1260 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1260 (0 : Fin 3) = raw7119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1260 raw7119; decide +kernel
    rw [heq]
    exact (canonical7119 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1260 (1 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1260 (1 : Fin 3) = raw7242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1260 raw7242; decide +kernel
    rw [heq]
    exact (canonical7242 hH).trans (sound287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1260 (2 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1260 (2 : Fin 3) = raw7243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1260 raw7243; decide +kernel
    rw [heq]
    exact (canonical7243 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1260 + (injectiveMoment H (mergeFirst pivotMatrix1260 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1260 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1260 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1260, value181, value287, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1261 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1261 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem sound1261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1261 = Sparse.eval value1261 (momentVector H) := by
  have heq : pivotMatrix1261 = (fun u v => node1261 (pivotPermutation1261 u) v) := by apply Matrix.ext; unfold pivotMatrix1261 node1261 pivotPermutation1261; decide +kernel
  have hmoment : injectiveMoment H node1261 = injectiveMoment H pivotMatrix1261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1261 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1261 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1261 (0 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1261 (0 : Fin 3) = raw7353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1261 raw7353; decide +kernel
    rw [heq]
    exact (canonical7353 hH).trans (sound284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1261 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1261 (1 : Fin 3) = raw7241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1261 raw7241; decide +kernel
    rw [heq]
    exact (canonical7241 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1261 (2 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1261 (2 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1261 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1261 + (injectiveMoment H (mergeFirst pivotMatrix1261 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1261 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1261 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1261, value174, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1262 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1262 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem sound1262 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1262 = Sparse.eval value1262 (momentVector H) := by
  have heq : pivotMatrix1262 = (fun u v => node1262 (pivotPermutation1262 u) v) := by apply Matrix.ext; unfold pivotMatrix1262 node1262 pivotPermutation1262; decide +kernel
  have hmoment : injectiveMoment H node1262 = injectiveMoment H pivotMatrix1262 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1262 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1262 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1262 (0 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1262 (0 : Fin 3) = raw7354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1262 raw7354; decide +kernel
    rw [heq]
    exact (canonical7354 hH).trans (sound293 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1262 (1 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1262 (1 : Fin 3) = raw7242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1262 raw7242; decide +kernel
    rw [heq]
    exact (canonical7242 hH).trans (sound287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1262 (2 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1262 (2 : Fin 3) = raw7241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1262 raw7241; decide +kernel
    rw [heq]
    exact (canonical7241 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1262 + (injectiveMoment H (mergeFirst pivotMatrix1262 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1262 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1262 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1262, value284, value287, value293, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1263 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![2, -2, 1, -1]]

theorem sound1263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1263 = Sparse.eval value1263 (momentVector H) := by
  have heq : pivotMatrix1263 = (fun u v => node1263.transpose (pivotPermutation1263 u) v) := by apply Matrix.ext; unfold pivotMatrix1263 node1263 pivotPermutation1263; decide +kernel
  have hmoment : injectiveMoment H node1263 = injectiveMoment H pivotMatrix1263 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1263 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1263 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1263 (0 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1263 (0 : Fin 3) = raw7478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1263 raw7478; decide +kernel
    rw [heq]
    exact (canonical7478 hH).trans (sound288 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1263 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1263 (1 : Fin 3) = raw9743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1263 raw9743; decide +kernel
    rw [heq]
    exact (canonical9743 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1263 (2 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1263 (2 : Fin 3) = raw9757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1263 raw9757; decide +kernel
    rw [heq]
    exact (canonical9757 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1263 + (injectiveMoment H (mergeFirst pivotMatrix1263 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1263 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1263 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1263, value279, value284, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1264 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1264 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

theorem sound1264 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1264 = Sparse.eval value1264 (momentVector H) := by
  have heq : pivotMatrix1264 = (fun u v => node1264 (pivotPermutation1264 u) v) := by apply Matrix.ext; unfold pivotMatrix1264 node1264 pivotPermutation1264; decide +kernel
  have hmoment : injectiveMoment H node1264 = injectiveMoment H pivotMatrix1264 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1264 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1264 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1264 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1264 (0 : Fin 3) = raw7824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1264 raw7824; decide +kernel
    rw [heq]
    exact (canonical7824 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1264 (1 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1264 (1 : Fin 3) = raw7243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1264 raw7243; decide +kernel
    rw [heq]
    exact (canonical7243 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1264 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1264 (2 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1264 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1264 + (injectiveMoment H (mergeFirst pivotMatrix1264 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1264 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1264 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1264, value291, value294, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1265 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1265 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, 0, -1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1]]

theorem sound1265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1265 = Sparse.eval value1265 (momentVector H) := by
  have heq : pivotMatrix1265 = (fun u v => node1265 (pivotPermutation1265 u) v) := by apply Matrix.ext; unfold pivotMatrix1265 node1265 pivotPermutation1265; decide +kernel
  have hmoment : injectiveMoment H node1265 = injectiveMoment H pivotMatrix1265 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1265 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1265 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1265 (0 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1265 (0 : Fin 3) = raw7869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1265 raw7869; decide +kernel
    rw [heq]
    exact (canonical7869 hH).trans (sound227 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1265 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1265 (1 : Fin 3) = raw7245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1265 raw7245; decide +kernel
    rw [heq]
    exact (canonical7245 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1265 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1265 (2 : Fin 3) = raw7218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1265 raw7218; decide +kernel
    rw [heq]
    exact (canonical7218 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1265 + (injectiveMoment H (mergeFirst pivotMatrix1265 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1265 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1265 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1265, value181, value227, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1266 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![2, -2, -3, 3]]

theorem sound1266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1266 = Sparse.eval value1266 (momentVector H) := by
  have heq : pivotMatrix1266 = (fun u v => node1266.transpose (pivotPermutation1266 u) v) := by apply Matrix.ext; unfold pivotMatrix1266 node1266 pivotPermutation1266; decide +kernel
  have hmoment : injectiveMoment H node1266 = injectiveMoment H pivotMatrix1266 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1266 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1266 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1266 (0 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1266 (0 : Fin 3) = raw7540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1266 raw7540; decide +kernel
    rw [heq]
    exact (canonical7540 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1266 (1 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1266 (1 : Fin 3) = raw9967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1266 raw9967; decide +kernel
    rw [heq]
    exact (canonical9967 hH).trans (sound162 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1266 (2 : Fin 3)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1266 (2 : Fin 3) = raw9979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1266 raw9979; decide +kernel
    rw [heq]
    exact (canonical9979 hH).trans (sound140 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1266 + (injectiveMoment H (mergeFirst pivotMatrix1266 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1266 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1266 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1266, value140, value162, value167, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1267 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1267 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

theorem sound1267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1267 = Sparse.eval value1267 (momentVector H) := by
  have heq : pivotMatrix1267 = (fun u v => node1267 (pivotPermutation1267 u) v) := by apply Matrix.ext; unfold pivotMatrix1267 node1267 pivotPermutation1267; decide +kernel
  have hmoment : injectiveMoment H node1267 = injectiveMoment H pivotMatrix1267 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1267 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1267 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1267 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1267 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (1 : Fin 3) = raw7249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw7249; decide +kernel
    rw [heq]
    exact (canonical7249 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1267 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (2 : Fin 3) = raw7223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw7223; decide +kernel
    rw [heq]
    exact (canonical7223 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1267 + (injectiveMoment H (mergeFirst pivotMatrix1267 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1267 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1267 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1267, value174, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1268 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1268 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, 0, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1]]

theorem sound1268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1268 = Sparse.eval value1268 (momentVector H) := by
  have heq : pivotMatrix1268 = (fun u v => node1268 (pivotPermutation1268 u) v) := by apply Matrix.ext; unfold pivotMatrix1268 node1268 pivotPermutation1268; decide +kernel
  have hmoment : injectiveMoment H node1268 = injectiveMoment H pivotMatrix1268 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1268 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1268 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1268 (0 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1268 (0 : Fin 3) = raw7827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1268 raw7827; decide +kernel
    rw [heq]
    exact (canonical7827 hH).trans (sound259 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1268 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1268 (1 : Fin 3) = raw7245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1268 raw7245; decide +kernel
    rw [heq]
    exact (canonical7245 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1268 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1268 (2 : Fin 3) = raw7223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1268 raw7223; decide +kernel
    rw [heq]
    exact (canonical7223 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1268 + (injectiveMoment H (mergeFirst pivotMatrix1268 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1268 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1268 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1268, value181, value259, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1269 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 3, -2, 0], ![2, -3, 0, 1]]

theorem sound1269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1269 = Sparse.eval value1269 (momentVector H) := by
  have heq : pivotMatrix1269 = (fun u v => node1269.transpose (pivotPermutation1269 u) v) := by apply Matrix.ext; unfold pivotMatrix1269 node1269 pivotPermutation1269; decide +kernel
  have hmoment : injectiveMoment H node1269 = injectiveMoment H pivotMatrix1269 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1269 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1269 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1269 (0 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1269 (0 : Fin 3) = raw7542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1269 raw7542; decide +kernel
    rw [heq]
    exact (canonical7542 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1269 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1269 (1 : Fin 3) = raw9968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1269 raw9968; decide +kernel
    rw [heq]
    exact (canonical9968 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1269 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1269 (2 : Fin 3) = raw9980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1269 raw9980; decide +kernel
    rw [heq]
    exact (canonical9980 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1269 + (injectiveMoment H (mergeFirst pivotMatrix1269 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1269 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1269 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1269, value198, value204, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1270 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 3, -1, -1], ![2, -3, -1, 2]]

theorem sound1270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1270 = Sparse.eval value1270 (momentVector H) := by
  have heq : pivotMatrix1270 = (fun u v => node1270.transpose (pivotPermutation1270 u) v) := by apply Matrix.ext; unfold pivotMatrix1270 node1270 pivotPermutation1270; decide +kernel
  have hmoment : injectiveMoment H node1270 = injectiveMoment H pivotMatrix1270 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1270 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1270 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1270 (0 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1270 (0 : Fin 3) = raw7543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1270 raw7543; decide +kernel
    rw [heq]
    exact (canonical7543 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1270 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1270 (1 : Fin 3) = raw9969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1270 raw9969; decide +kernel
    rw [heq]
    exact (canonical9969 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1270 (2 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1270 (2 : Fin 3) = raw9981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1270 raw9981; decide +kernel
    rw [heq]
    exact (canonical9981 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1270 + (injectiveMoment H (mergeFirst pivotMatrix1270 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1270 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1270 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1270, value170, value198, value223, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1271 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 3, 0, -2], ![2, -3, -2, 3]]

theorem sound1271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1271 = Sparse.eval value1271 (momentVector H) := by
  have heq : pivotMatrix1271 = (fun u v => node1271.transpose (pivotPermutation1271 u) v) := by apply Matrix.ext; unfold pivotMatrix1271 node1271 pivotPermutation1271; decide +kernel
  have hmoment : injectiveMoment H node1271 = injectiveMoment H pivotMatrix1271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1271 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1271 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1271 (0 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1271 (0 : Fin 3) = raw7544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1271 raw7544; decide +kernel
    rw [heq]
    exact (canonical7544 hH).trans (sound196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1271 (1 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1271 (1 : Fin 3) = raw9970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1271 raw9970; decide +kernel
    rw [heq]
    exact (canonical9970 hH).trans (sound163 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1271 (2 : Fin 3)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1271 (2 : Fin 3) = raw9982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1271 raw9982; decide +kernel
    rw [heq]
    exact (canonical9982 hH).trans (sound141 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1271 + (injectiveMoment H (mergeFirst pivotMatrix1271 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1271 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1271 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1271, value141, value163, value196, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1272 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, 4, -2, -1], ![2, -4, 1, 1]]

theorem sound1272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1272 = Sparse.eval value1272 (momentVector H) := by
  have heq : pivotMatrix1272 = (fun u v => node1272.transpose (pivotPermutation1272 u) v) := by apply Matrix.ext; unfold pivotMatrix1272 node1272 pivotPermutation1272; decide +kernel
  have hmoment : injectiveMoment H node1272 = injectiveMoment H pivotMatrix1272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1272 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1272 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1272 (0 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1272 (0 : Fin 3) = raw7480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1272 raw7480; decide +kernel
    rw [heq]
    exact (canonical7480 hH).trans (sound286 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1272 (1 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1272 (1 : Fin 3) = raw9746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1272 raw9746; decide +kernel
    rw [heq]
    exact (canonical9746 hH).trans (sound281 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1272 (2 : Fin 3)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1272 (2 : Fin 3) = raw9761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1272 raw9761; decide +kernel
    rw [heq]
    exact (canonical9761 hH).trans (sound286 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1272 + (injectiveMoment H (mergeFirst pivotMatrix1272 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1272 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1272 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1272, value281, value286, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1273 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-1, 4, -3, 0], ![2, -4, 1, 1]]

theorem sound1273 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1273 = Sparse.eval value1273 (momentVector H) := by
  have heq : pivotMatrix1273 = (fun u v => node1273.transpose (pivotPermutation1273 u) v) := by apply Matrix.ext; unfold pivotMatrix1273 node1273 pivotPermutation1273; decide +kernel
  have hmoment : injectiveMoment H node1273 = injectiveMoment H pivotMatrix1273 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1273 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1273 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1273 (0 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1273 (0 : Fin 3) = raw7545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1273 raw7545; decide +kernel
    rw [heq]
    exact (canonical7545 hH).trans (sound190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1273 (1 : Fin 3)) =
      Sparse.eval value164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1273 (1 : Fin 3) = raw9971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1273 raw9971; decide +kernel
    rw [heq]
    exact (canonical9971 hH).trans (sound164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1273 (2 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1273 (2 : Fin 3) = raw9983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1273 raw9983; decide +kernel
    rw [heq]
    exact (canonical9983 hH).trans (sound171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1273 + (injectiveMoment H (mergeFirst pivotMatrix1273 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1273 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1273 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1273, value164, value171, value190, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1274 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -3, 1, 3], ![2, 2, -2, -2]]

theorem sound1274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1274 = Sparse.eval value1274 (momentVector H) := by
  have heq : pivotMatrix1274 = (fun u v => node1274.transpose (pivotPermutation1274 u) v) := by apply Matrix.ext; unfold pivotMatrix1274 node1274 pivotPermutation1274; decide +kernel
  have hmoment : injectiveMoment H node1274 = injectiveMoment H pivotMatrix1274 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1274 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1274 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1274 (0 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1274 (0 : Fin 3) = raw7909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1274 raw7909; decide +kernel
    rw [heq]
    exact (canonical7909 hH).trans (sound260 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1274 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1274 (1 : Fin 3) = raw10095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1274 raw10095; decide +kernel
    rw [heq]
    exact (canonical10095 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1274 (2 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1274 (2 : Fin 3) = raw10101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1274 raw10101; decide +kernel
    rw [heq]
    exact (canonical10101 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1274 + (injectiveMoment H (mergeFirst pivotMatrix1274 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1274 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1274 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1274, value152, value180, value260, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1275 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -3, 3, 1], ![2, 2, -4, 0]]

theorem sound1275 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1275 = Sparse.eval value1275 (momentVector H) := by
  have heq : pivotMatrix1275 = (fun u v => node1275.transpose (pivotPermutation1275 u) v) := by apply Matrix.ext; unfold pivotMatrix1275 node1275 pivotPermutation1275; decide +kernel
  have hmoment : injectiveMoment H node1275 = injectiveMoment H pivotMatrix1275 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1275 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1275 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1275 (0 : Fin 3)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1275 (0 : Fin 3) = raw7911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1275 raw7911; decide +kernel
    rw [heq]
    exact (canonical7911 hH).trans (sound247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1275 (1 : Fin 3)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1275 (1 : Fin 3) = raw10096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1275 raw10096; decide +kernel
    rw [heq]
    exact (canonical10096 hH).trans (sound211 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1275 (2 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1275 (2 : Fin 3) = raw10102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1275 raw10102; decide +kernel
    rw [heq]
    exact (canonical10102 hH).trans (sound228 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1275 + (injectiveMoment H (mergeFirst pivotMatrix1275 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1275 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1275 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1275, value211, value228, value247, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1276 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 1, 2], ![2, 1, -2, -1]]

theorem sound1276 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1276 = Sparse.eval value1276 (momentVector H) := by
  have heq : pivotMatrix1276 = (fun u v => node1276.transpose (pivotPermutation1276 u) v) := by apply Matrix.ext; unfold pivotMatrix1276 node1276 pivotPermutation1276; decide +kernel
  have hmoment : injectiveMoment H node1276 = injectiveMoment H pivotMatrix1276 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1276 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1276 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1276 (0 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1276 (0 : Fin 3) = raw7913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1276 raw7913; decide +kernel
    rw [heq]
    exact (canonical7913 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1276 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1276 (1 : Fin 3) = raw10097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1276 raw10097; decide +kernel
    rw [heq]
    exact (canonical10097 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1276 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1276 (2 : Fin 3) = raw10103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1276 raw10103; decide +kernel
    rw [heq]
    exact (canonical10103 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1276 + (injectiveMoment H (mergeFirst pivotMatrix1276 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1276 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1276 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1276, value184, value210, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1277 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 2, 1], ![2, 1, -3, 0]]

theorem sound1277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1277 = Sparse.eval value1277 (momentVector H) := by
  have heq : pivotMatrix1277 = (fun u v => node1277.transpose (pivotPermutation1277 u) v) := by apply Matrix.ext; unfold pivotMatrix1277 node1277 pivotPermutation1277; decide +kernel
  have hmoment : injectiveMoment H node1277 = injectiveMoment H pivotMatrix1277 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1277 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1277 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1277 (0 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (0 : Fin 3) = raw7914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw7914; decide +kernel
    rw [heq]
    exact (canonical7914 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1277 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (1 : Fin 3) = raw10098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw10098; decide +kernel
    rw [heq]
    exact (canonical10098 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1277 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (2 : Fin 3) = raw10104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw10104; decide +kernel
    rw [heq]
    exact (canonical10104 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1277 + (injectiveMoment H (mergeFirst pivotMatrix1277 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1277 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1277 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1277, value212, value229, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1278 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, -2, 3, 0], ![2, 1, -4, 1]]

theorem sound1278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1278 = Sparse.eval value1278 (momentVector H) := by
  have heq : pivotMatrix1278 = (fun u v => node1278.transpose (pivotPermutation1278 u) v) := by apply Matrix.ext; unfold pivotMatrix1278 node1278 pivotPermutation1278; decide +kernel
  have hmoment : injectiveMoment H node1278 = injectiveMoment H pivotMatrix1278 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1278 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1278 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1278 (0 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1278 (0 : Fin 3) = raw7915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1278 raw7915; decide +kernel
    rw [heq]
    exact (canonical7915 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1278 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1278 (1 : Fin 3) = raw10099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1278 raw10099; decide +kernel
    rw [heq]
    exact (canonical10099 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1278 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1278 (2 : Fin 3) = raw10105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1278 raw10105; decide +kernel
    rw [heq]
    exact (canonical10105 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1278 + (injectiveMoment H (mergeFirst pivotMatrix1278 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1278 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1278 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1278, value206, value225, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1279 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![2, -2, -3, 3]]

theorem sound1279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1279 = Sparse.eval value1279 (momentVector H) := by
  have heq : pivotMatrix1279 = (fun u v => node1279.transpose (pivotPermutation1279 u) v) := by apply Matrix.ext; unfold pivotMatrix1279 node1279 pivotPermutation1279; decide +kernel
  have hmoment : injectiveMoment H node1279 = injectiveMoment H pivotMatrix1279 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1279 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1279 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1279 (0 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1279 (0 : Fin 3) = raw7917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1279 raw7917; decide +kernel
    rw [heq]
    exact (canonical7917 hH).trans (sound258 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1279 (1 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1279 (1 : Fin 3) = raw10100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1279 raw10100; decide +kernel
    rw [heq]
    exact (canonical10100 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1279 (2 : Fin 3)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1279 (2 : Fin 3) = raw10106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1279 raw10106; decide +kernel
    rw [heq]
    exact (canonical10106 hH).trans (sound144 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1279 + (injectiveMoment H (mergeFirst pivotMatrix1279 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1279 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1279 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1279, value144, value167, value258, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
