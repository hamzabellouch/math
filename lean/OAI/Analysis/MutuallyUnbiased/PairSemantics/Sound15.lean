import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical207
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical260
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical262
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical263

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation960 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix960 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem sound960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node960 = Sparse.eval value960 (momentVector H) := by
  have heq : pivotMatrix960 = (fun u v => node960 (pivotPermutation960 u) v) := by apply Matrix.ext; unfold pivotMatrix960 node960 pivotPermutation960; decide +kernel
  have hmoment : injectiveMoment H node960 = injectiveMoment H pivotMatrix960 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix960 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix960 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix960 (0 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix960 (0 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix960 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix960 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix960 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix960 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix960 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix960 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix960 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node960 + (injectiveMoment H (mergeFirst pivotMatrix960 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix960 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix960 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value960, value176, value188, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation961 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix961 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 4, -4], ![1, 1, -2, 0]]

theorem sound961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node961 = Sparse.eval value961 (momentVector H) := by
  have heq : pivotMatrix961 = (fun u v => node961 (pivotPermutation961 u) v) := by apply Matrix.ext; unfold pivotMatrix961 node961 pivotPermutation961; decide +kernel
  have hmoment : injectiveMoment H node961 = injectiveMoment H pivotMatrix961 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix961 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix961 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix961 (0 : Fin 3)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix961 (0 : Fin 3) = raw6095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix961 raw6095; decide +kernel
    rw [heq]
    exact (canonical6095 hH).trans (sound157 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix961 (1 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix961 (1 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix961 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix961 (2 : Fin 3)) =
      Sparse.eval value90 (momentVector H) := by
    have heq : mergeFirst pivotMatrix961 (2 : Fin 3) = raw6299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix961 raw6299; decide +kernel
    rw [heq]
    exact (canonical6299 hH).trans (sound90 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node961 + (injectiveMoment H (mergeFirst pivotMatrix961 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix961 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix961 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value961, value157, value188, value90, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation962 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix962 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem sound962 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node962 = Sparse.eval value962 (momentVector H) := by
  have heq : pivotMatrix962 = (fun u v => node962 (pivotPermutation962 u) v) := by apply Matrix.ext; unfold pivotMatrix962 node962 pivotPermutation962; decide +kernel
  have hmoment : injectiveMoment H node962 = injectiveMoment H pivotMatrix962 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix962 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix962 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix962 (0 : Fin 3)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix962 (0 : Fin 3) = raw6103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix962 raw6103; decide +kernel
    rw [heq]
    exact (canonical6103 hH).trans (sound270 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix962 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix962 (1 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix962 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix962 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix962 (2 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix962 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node962 + (injectiveMoment H (mergeFirst pivotMatrix962 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix962 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix962 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value962, value173, value270, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation963 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix963 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem sound963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node963 = Sparse.eval value963 (momentVector H) := by
  have heq : pivotMatrix963 = (fun u v => node963 (pivotPermutation963 u) v) := by apply Matrix.ext; unfold pivotMatrix963 node963 pivotPermutation963; decide +kernel
  have hmoment : injectiveMoment H node963 = injectiveMoment H pivotMatrix963 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix963 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix963 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix963 (0 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix963 (0 : Fin 3) = raw6105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix963 raw6105; decide +kernel
    rw [heq]
    exact (canonical6105 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix963 (1 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix963 (1 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix963 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix963 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix963 (2 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix963 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node963 + (injectiveMoment H (mergeFirst pivotMatrix963 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix963 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix963 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value963, value254, value271, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation964 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix964 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound964 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node964 = Sparse.eval value964 (momentVector H) := by
  have heq : pivotMatrix964 = (fun u v => node964 (pivotPermutation964 u) v) := by apply Matrix.ext; unfold pivotMatrix964 node964 pivotPermutation964; decide +kernel
  have hmoment : injectiveMoment H node964 = injectiveMoment H pivotMatrix964 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix964 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix964 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix964 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix964 (0 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix964 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix964 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix964 (1 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix964 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix964 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix964 (2 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix964 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node964 + (injectiveMoment H (mergeFirst pivotMatrix964 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix964 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix964 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value964, value150, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation965 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix965 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem sound965 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node965 = Sparse.eval value965 (momentVector H) := by
  have heq : pivotMatrix965 = (fun u v => node965 (pivotPermutation965 u) v) := by apply Matrix.ext; unfold pivotMatrix965 node965 pivotPermutation965; decide +kernel
  have hmoment : injectiveMoment H node965 = injectiveMoment H pivotMatrix965 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix965 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix965 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix965 (0 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix965 (0 : Fin 3) = raw6112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix965 raw6112; decide +kernel
    rw [heq]
    exact (canonical6112 hH).trans (sound228 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix965 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix965 (1 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix965 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix965 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix965 (2 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix965 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node965 + (injectiveMoment H (mergeFirst pivotMatrix965 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix965 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix965 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value965, value170, value228, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation966 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix966 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem sound966 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node966 = Sparse.eval value966 (momentVector H) := by
  have heq : pivotMatrix966 = (fun u v => node966 (pivotPermutation966 u) v) := by apply Matrix.ext; unfold pivotMatrix966 node966 pivotPermutation966; decide +kernel
  have hmoment : injectiveMoment H node966 = injectiveMoment H pivotMatrix966 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix966 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix966 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix966 (0 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix966 (0 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix966 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix966 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix966 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix966 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix966 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix966 (2 : Fin 3) = raw6283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix966 raw6283; decide +kernel
    rw [heq]
    exact (canonical6283 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node966 + (injectiveMoment H (mergeFirst pivotMatrix966 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix966 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix966 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value966, value176, value271, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation967 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix967 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem sound967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node967 = Sparse.eval value967 (momentVector H) := by
  have heq : pivotMatrix967 = (fun u v => node967 (pivotPermutation967 u) v) := by apply Matrix.ext; unfold pivotMatrix967 node967 pivotPermutation967; decide +kernel
  have hmoment : injectiveMoment H node967 = injectiveMoment H pivotMatrix967 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix967 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix967 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix967 (0 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix967 (0 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix967 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix967 (1 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix967 (1 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix967 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix967 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix967 (2 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix967 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node967 + (injectiveMoment H (mergeFirst pivotMatrix967 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix967 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix967 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value967, value176, value188, value207, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation968 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix968 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem sound968 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node968 = Sparse.eval value968 (momentVector H) := by
  have heq : pivotMatrix968 = (fun u v => node968 (pivotPermutation968 u) v) := by apply Matrix.ext; unfold pivotMatrix968 node968 pivotPermutation968; decide +kernel
  have hmoment : injectiveMoment H node968 = injectiveMoment H pivotMatrix968 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix968 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix968 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix968 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix968 (0 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix968 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix968 (1 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix968 (1 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix968 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix968 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix968 (2 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix968 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node968 + (injectiveMoment H (mergeFirst pivotMatrix968 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix968 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix968 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value968, value173, value185, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation969 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix969 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem sound969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node969 = Sparse.eval value969 (momentVector H) := by
  have heq : pivotMatrix969 = (fun u v => node969 (pivotPermutation969 u) v) := by apply Matrix.ext; unfold pivotMatrix969 node969 pivotPermutation969; decide +kernel
  have hmoment : injectiveMoment H node969 = injectiveMoment H pivotMatrix969 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix969 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix969 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix969 (0 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix969 (0 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix969 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix969 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix969 (1 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix969 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix969 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix969 (2 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix969 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node969 + (injectiveMoment H (mergeFirst pivotMatrix969 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix969 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix969 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value969, value271, value285, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation970 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix970 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem sound970 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node970 = Sparse.eval value970 (momentVector H) := by
  have heq : pivotMatrix970 = (fun u v => node970 (pivotPermutation970 u) v) := by apply Matrix.ext; unfold pivotMatrix970 node970 pivotPermutation970; decide +kernel
  have hmoment : injectiveMoment H node970 = injectiveMoment H pivotMatrix970 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix970 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix970 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix970 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix970 (0 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix970 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix970 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix970 (1 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix970 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix970 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix970 (2 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix970 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node970 + (injectiveMoment H (mergeFirst pivotMatrix970 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix970 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix970 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value970, value271, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation971 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix971 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, -1, 2, -2]]

theorem sound971 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node971 = Sparse.eval value971 (momentVector H) := by
  have heq : pivotMatrix971 = (fun u v => node971 (pivotPermutation971 u) v) := by apply Matrix.ext; unfold pivotMatrix971 node971 pivotPermutation971; decide +kernel
  have hmoment : injectiveMoment H node971 = injectiveMoment H pivotMatrix971 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix971 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix971 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix971 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix971 (0 : Fin 3) = raw6557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix971 raw6557; decide +kernel
    rw [heq]
    exact (canonical6557 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix971 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix971 (1 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix971 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix971 (2 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix971 (2 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix971 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node971 + (injectiveMoment H (mergeFirst pivotMatrix971 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix971 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix971 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value971, value170, value203, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation972 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix972 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -1, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem sound972 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node972 = Sparse.eval value972 (momentVector H) := by
  have heq : pivotMatrix972 = (fun u v => node972 (pivotPermutation972 u) v) := by apply Matrix.ext; unfold pivotMatrix972 node972 pivotPermutation972; decide +kernel
  have hmoment : injectiveMoment H node972 = injectiveMoment H pivotMatrix972 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix972 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix972 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix972 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix972 (0 : Fin 3) = raw6559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix972 raw6559; decide +kernel
    rw [heq]
    exact (canonical6559 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix972 (1 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix972 (1 : Fin 3) = raw6333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix972 raw6333; decide +kernel
    rw [heq]
    exact (canonical6333 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix972 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix972 (2 : Fin 3) = raw6332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix972 raw6332; decide +kernel
    rw [heq]
    exact (canonical6332 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node972 + (injectiveMoment H (mergeFirst pivotMatrix972 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix972 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix972 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value972, value181, value244, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation973 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix973 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, 2, -2, 1], ![3, -2, 1, -2]]

theorem sound973 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node973 = Sparse.eval value973 (momentVector H) := by
  have heq : pivotMatrix973 = (fun u v => node973.transpose (pivotPermutation973 u) v) := by apply Matrix.ext; unfold pivotMatrix973 node973 pivotPermutation973; decide +kernel
  have hmoment : injectiveMoment H node973 = injectiveMoment H pivotMatrix973 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix973 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix973 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix973 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (0 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix973 (1 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (1 : Fin 3) = raw7468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw7468; decide +kernel
    rw [heq]
    exact (canonical7468 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix973 (2 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix973 (2 : Fin 3) = raw7478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix973 raw7478; decide +kernel
    rw [heq]
    exact (canonical7478 hH).trans (sound288 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node973 + (injectiveMoment H (mergeFirst pivotMatrix973 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix973 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix973 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value973, value184, value274, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation974 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix974 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

theorem sound974 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node974 = Sparse.eval value974 (momentVector H) := by
  have heq : pivotMatrix974 = (fun u v => node974 (pivotPermutation974 u) v) := by apply Matrix.ext; unfold pivotMatrix974 node974 pivotPermutation974; decide +kernel
  have hmoment : injectiveMoment H node974 = injectiveMoment H pivotMatrix974 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix974 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix974 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix974 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix974 (0 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix974 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix974 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix974 (1 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix974 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix974 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix974 (2 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix974 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node974 + (injectiveMoment H (mergeFirst pivotMatrix974 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix974 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix974 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value974, value176, value271, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation975 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix975 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, 2, -2, 1], ![3, -2, 0, -1]]

theorem sound975 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node975 = Sparse.eval value975 (momentVector H) := by
  have heq : pivotMatrix975 = (fun u v => node975.transpose (pivotPermutation975 u) v) := by apply Matrix.ext; unfold pivotMatrix975 node975 pivotPermutation975; decide +kernel
  have hmoment : injectiveMoment H node975 = injectiveMoment H pivotMatrix975 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix975 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix975 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix975 (0 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix975 (0 : Fin 3) = raw4171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix975 raw4171; decide +kernel
    rw [heq]
    exact (canonical4171 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix975 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix975 (1 : Fin 3) = raw7522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix975 raw7522; decide +kernel
    rw [heq]
    exact (canonical7522 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix975 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix975 (2 : Fin 3) = raw7537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix975 raw7537; decide +kernel
    rw [heq]
    exact (canonical7537 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node975 + (injectiveMoment H (mergeFirst pivotMatrix975 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix975 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix975 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value975, value177, value203, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation976 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, 2, 0, -1], ![3, -2, -2, 1]]

theorem sound976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node976 = Sparse.eval value976 (momentVector H) := by
  have heq : pivotMatrix976 = (fun u v => node976.transpose (pivotPermutation976 u) v) := by apply Matrix.ext; unfold pivotMatrix976 node976 pivotPermutation976; decide +kernel
  have hmoment : injectiveMoment H node976 = injectiveMoment H pivotMatrix976 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix976 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix976 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix976 (0 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix976 (0 : Fin 3) = raw4172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix976 raw4172; decide +kernel
    rw [heq]
    exact (canonical4172 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix976 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix976 (1 : Fin 3) = raw7524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix976 raw7524; decide +kernel
    rw [heq]
    exact (canonical7524 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix976 (2 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix976 (2 : Fin 3) = raw7539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix976 raw7539; decide +kernel
    rw [heq]
    exact (canonical7539 hH).trans (sound202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node976 + (injectiveMoment H (mergeFirst pivotMatrix976 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix976 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix976 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value976, value169, value202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation977 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix977 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1]]

theorem sound977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node977 = Sparse.eval value977 (momentVector H) := by
  have heq : pivotMatrix977 = (fun u v => node977 (pivotPermutation977 u) v) := by apply Matrix.ext; unfold pivotMatrix977 node977 pivotPermutation977; decide +kernel
  have hmoment : injectiveMoment H node977 = injectiveMoment H pivotMatrix977 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix977 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix977 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (1 : Fin 3) = raw6338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6338; decide +kernel
    rw [heq]
    exact (canonical6338 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node977 + (injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value977, value173, value188, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation978 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix978 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![1, 0, -1, 0]]

theorem sound978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node978 = Sparse.eval value978 (momentVector H) := by
  have heq : pivotMatrix978 = (fun u v => node978 (pivotPermutation978 u) v) := by apply Matrix.ext; unfold pivotMatrix978 node978 pivotPermutation978; decide +kernel
  have hmoment : injectiveMoment H node978 = injectiveMoment H pivotMatrix978 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix978 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix978 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix978 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix978 (0 : Fin 3) = raw7108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix978 raw7108; decide +kernel
    rw [heq]
    exact (canonical7108 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix978 (1 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix978 (1 : Fin 3) = raw6328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix978 raw6328; decide +kernel
    rw [heq]
    exact (canonical6328 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix978 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix978 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix978 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node978 + (injectiveMoment H (mergeFirst pivotMatrix978 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix978 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix978 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value978, value188, value285, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation979 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix979 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

theorem sound979 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node979 = Sparse.eval value979 (momentVector H) := by
  have heq : pivotMatrix979 = (fun u v => node979 (pivotPermutation979 u) v) := by apply Matrix.ext; unfold pivotMatrix979 node979 pivotPermutation979; decide +kernel
  have hmoment : injectiveMoment H node979 = injectiveMoment H pivotMatrix979 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix979 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix979 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix979 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix979 (0 : Fin 3) = raw8047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix979 raw8047; decide +kernel
    rw [heq]
    exact (canonical8047 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix979 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix979 (1 : Fin 3) = raw6336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix979 raw6336; decide +kernel
    rw [heq]
    exact (canonical6336 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix979 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix979 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix979 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node979 + (injectiveMoment H (mergeFirst pivotMatrix979 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix979 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix979 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value979, value170, value188, value37, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation980 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-1, 3, -1, -1], ![3, -3, -1, 1]]

theorem sound980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node980 = Sparse.eval value980 (momentVector H) := by
  have heq : pivotMatrix980 = (fun u v => node980.transpose (pivotPermutation980 u) v) := by apply Matrix.ext; unfold pivotMatrix980 node980 pivotPermutation980; decide +kernel
  have hmoment : injectiveMoment H node980 = injectiveMoment H pivotMatrix980 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix980 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix980 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix980 (0 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix980 (0 : Fin 3) = raw4174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix980 raw4174; decide +kernel
    rw [heq]
    exact (canonical4174 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix980 (1 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix980 (1 : Fin 3) = raw7525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix980 raw7525; decide +kernel
    rw [heq]
    exact (canonical7525 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix980 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix980 (2 : Fin 3) = raw7543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix980 raw7543; decide +kernel
    rw [heq]
    exact (canonical7543 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node980 + (injectiveMoment H (mergeFirst pivotMatrix980 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix980 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix980 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value980, value170, value222, value223, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation981 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix981 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

theorem sound981 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node981 = Sparse.eval value981 (momentVector H) := by
  have heq : pivotMatrix981 = (fun u v => node981 (pivotPermutation981 u) v) := by apply Matrix.ext; unfold pivotMatrix981 node981 pivotPermutation981; decide +kernel
  have hmoment : injectiveMoment H node981 = injectiveMoment H pivotMatrix981 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix981 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix981 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix981 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix981 (0 : Fin 3) = raw8302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix981 raw8302; decide +kernel
    rw [heq]
    exact (canonical8302 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix981 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix981 (1 : Fin 3) = raw6338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix981 raw6338; decide +kernel
    rw [heq]
    exact (canonical6338 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix981 (2 : Fin 3)) =
      Sparse.eval value90 (momentVector H) := by
    have heq : mergeFirst pivotMatrix981 (2 : Fin 3) = raw6299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix981 raw6299; decide +kernel
    rw [heq]
    exact (canonical6299 hH).trans (sound90 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node981 + (injectiveMoment H (mergeFirst pivotMatrix981 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix981 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix981 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value981, value173, value59, value90, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation982 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix982 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![1, -1, 3, -3]]

theorem sound982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node982 = Sparse.eval value982 (momentVector H) := by
  have heq : pivotMatrix982 = (fun u v => node982 (pivotPermutation982 u) v) := by apply Matrix.ext; unfold pivotMatrix982 node982 pivotPermutation982; decide +kernel
  have hmoment : injectiveMoment H node982 = injectiveMoment H pivotMatrix982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix982 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix982 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (0 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix982 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (1 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix982 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (2 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node982 + (injectiveMoment H (mergeFirst pivotMatrix982 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix982 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix982 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value982, value170, value173, value174, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation983 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -2, 1, 2], ![3, 1, -2, -2]]

theorem sound983 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node983 = Sparse.eval value983 (momentVector H) := by
  have heq : pivotMatrix983 = (fun u v => node983.transpose (pivotPermutation983 u) v) := by apply Matrix.ext; unfold pivotMatrix983 node983 pivotPermutation983; decide +kernel
  have hmoment : injectiveMoment H node983 = injectiveMoment H pivotMatrix983 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix983 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix983 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix983 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix983 (0 : Fin 3) = raw4971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix983 raw4971; decide +kernel
    rw [heq]
    exact (canonical4971 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix983 (1 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix983 (1 : Fin 3) = raw7904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix983 raw7904; decide +kernel
    rw [heq]
    exact (canonical7904 hH).trans (sound262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix983 (2 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix983 (2 : Fin 3) = raw7913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix983 raw7913; decide +kernel
    rw [heq]
    exact (canonical7913 hH).trans (sound276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node983 + (injectiveMoment H (mergeFirst pivotMatrix983 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix983 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix983 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value983, value184, value262, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation984 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -2, 2, 1], ![3, 1, -3, -1]]

theorem sound984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node984 = Sparse.eval value984 (momentVector H) := by
  have heq : pivotMatrix984 = (fun u v => node984.transpose (pivotPermutation984 u) v) := by apply Matrix.ext; unfold pivotMatrix984 node984 pivotPermutation984; decide +kernel
  have hmoment : injectiveMoment H node984 = injectiveMoment H pivotMatrix984 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix984 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix984 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix984 (0 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix984 (0 : Fin 3) = raw4972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix984 raw4972; decide +kernel
    rw [heq]
    exact (canonical4972 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix984 (1 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix984 (1 : Fin 3) = raw7905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix984 raw7905; decide +kernel
    rw [heq]
    exact (canonical7905 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix984 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix984 (2 : Fin 3) = raw7914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix984 raw7914; decide +kernel
    rw [heq]
    exact (canonical7914 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node984 + (injectiveMoment H (mergeFirst pivotMatrix984 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix984 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix984 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value984, value180, value260, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation985 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix985 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

theorem sound985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node985 = Sparse.eval value985 (momentVector H) := by
  have heq : pivotMatrix985 = (fun u v => node985 (pivotPermutation985 u) v) := by apply Matrix.ext; unfold pivotMatrix985 node985 pivotPermutation985; decide +kernel
  have hmoment : injectiveMoment H node985 = injectiveMoment H pivotMatrix985 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix985 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix985 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix985 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix985 (0 : Fin 3) = raw8048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix985 raw8048; decide +kernel
    rw [heq]
    exact (canonical8048 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix985 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix985 (1 : Fin 3) = raw6337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix985 raw6337; decide +kernel
    rw [heq]
    exact (canonical6337 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix985 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix985 (2 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix985 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node985 + (injectiveMoment H (mergeFirst pivotMatrix985 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix985 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix985 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value985, value173, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation986 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix986 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem sound986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node986 = Sparse.eval value986 (momentVector H) := by
  have heq : pivotMatrix986 = (fun u v => node986 (pivotPermutation986 u) v) := by apply Matrix.ext; unfold pivotMatrix986 node986 pivotPermutation986; decide +kernel
  have hmoment : injectiveMoment H node986 = injectiveMoment H pivotMatrix986 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix986 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix986 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix986 (0 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix986 (0 : Fin 3) = raw7121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix986 raw7121; decide +kernel
    rw [heq]
    exact (canonical7121 hH).trans (sound243 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix986 (1 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix986 (1 : Fin 3) = raw6333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix986 raw6333; decide +kernel
    rw [heq]
    exact (canonical6333 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix986 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix986 (2 : Fin 3) = raw6329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix986 raw6329; decide +kernel
    rw [heq]
    exact (canonical6329 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node986 + (injectiveMoment H (mergeFirst pivotMatrix986 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix986 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix986 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value986, value173, value243, value244, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation987 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, 1, 1, -1], ![3, -2, -2, 1]]

theorem sound987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node987 = Sparse.eval value987 (momentVector H) := by
  have heq : pivotMatrix987 = (fun u v => node987.transpose (pivotPermutation987 u) v) := by apply Matrix.ext; unfold pivotMatrix987 node987 pivotPermutation987; decide +kernel
  have hmoment : injectiveMoment H node987 = injectiveMoment H pivotMatrix987 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix987 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix987 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix987 (0 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix987 (0 : Fin 3) = raw4973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix987 raw4973; decide +kernel
    rw [heq]
    exact (canonical4973 hH).trans (sound175 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix987 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix987 (1 : Fin 3) = raw7907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix987 raw7907; decide +kernel
    rw [heq]
    exact (canonical7907 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix987 (2 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix987 (2 : Fin 3) = raw7916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix987 raw7916; decide +kernel
    rw [heq]
    exact (canonical7916 hH).trans (sound275 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node987 + (injectiveMoment H (mergeFirst pivotMatrix987 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix987 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix987 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value987, value175, value275, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation988 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix988 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![0, 1, 2, -3], ![2, 1, -4, 1]]

theorem sound988 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node988 = Sparse.eval value988 (momentVector H) := by
  have heq : pivotMatrix988 = (fun u v => node988.transpose (pivotPermutation988 u) v) := by apply Matrix.ext; unfold pivotMatrix988 node988 pivotPermutation988; decide +kernel
  have hmoment : injectiveMoment H node988 = injectiveMoment H pivotMatrix988 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix988 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix988 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix988 (0 : Fin 3)) =
      Sparse.eval value112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix988 (0 : Fin 3) = raw1325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix988 raw1325; decide +kernel
    rw [heq]
    exact (canonical1325 hH).trans (sound112 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix988 (1 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix988 (1 : Fin 3) = raw5818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix988 raw5818; decide +kernel
    rw [heq]
    exact (canonical5818 hH).trans (sound134 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix988 (2 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix988 (2 : Fin 3) = raw5841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix988 raw5841; decide +kernel
    rw [heq]
    exact (canonical5841 hH).trans (sound106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node988 + (injectiveMoment H (mergeFirst pivotMatrix988 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix988 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix988 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value988, value106, value112, value134, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation989 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![0, 3, -3, 0], ![2, -1, 1, -2]]

theorem sound989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node989 = Sparse.eval value989 (momentVector H) := by
  have heq : pivotMatrix989 = (fun u v => node989.transpose (pivotPermutation989 u) v) := by apply Matrix.ext; unfold pivotMatrix989 node989 pivotPermutation989; decide +kernel
  have hmoment : injectiveMoment H node989 = injectiveMoment H pivotMatrix989 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix989 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix989 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix989 (0 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix989 (0 : Fin 3) = raw1329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix989 raw1329; decide +kernel
    rw [heq]
    exact (canonical1329 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix989 (1 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix989 (1 : Fin 3) = raw5820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix989 raw5820; decide +kernel
    rw [heq]
    exact (canonical5820 hH).trans (sound159 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix989 (2 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix989 (2 : Fin 3) = raw5844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix989 raw5844; decide +kernel
    rw [heq]
    exact (canonical5844 hH).trans (sound259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node989 + (injectiveMoment H (mergeFirst pivotMatrix989 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix989 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix989 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value989, value101, value159, value259, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation990 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![0, 3, -1, -2], ![2, -1, -2, 1]]

theorem sound990 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node990 = Sparse.eval value990 (momentVector H) := by
  have heq : pivotMatrix990 = (fun u v => node990.transpose (pivotPermutation990 u) v) := by apply Matrix.ext; unfold pivotMatrix990 node990 pivotPermutation990; decide +kernel
  have hmoment : injectiveMoment H node990 = injectiveMoment H pivotMatrix990 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix990 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix990 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix990 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix990 (0 : Fin 3) = raw1335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix990 raw1335; decide +kernel
    rw [heq]
    exact (canonical1335 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix990 (1 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix990 (1 : Fin 3) = raw5993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix990 raw5993; decide +kernel
    rw [heq]
    exact (canonical5993 hH).trans (sound109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix990 (2 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix990 (2 : Fin 3) = raw5995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix990 raw5995; decide +kernel
    rw [heq]
    exact (canonical5995 hH).trans (sound107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node990 + (injectiveMoment H (mergeFirst pivotMatrix990 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix990 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix990 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value990, value103, value107, value109, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation991 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 2, 0], ![2, 3, -3, -2]]

theorem sound991 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node991 = Sparse.eval value991 (momentVector H) := by
  have heq : pivotMatrix991 = (fun u v => node991.transpose (pivotPermutation991 u) v) := by apply Matrix.ext; unfold pivotMatrix991 node991 pivotPermutation991; decide +kernel
  have hmoment : injectiveMoment H node991 = injectiveMoment H pivotMatrix991 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix991 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix991 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix991 (0 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix991 (0 : Fin 3) = raw2151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix991 raw2151; decide +kernel
    rw [heq]
    exact (canonical2151 hH).trans (sound162 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix991 (1 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix991 (1 : Fin 3) = raw6578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix991 raw6578; decide +kernel
    rw [heq]
    exact (canonical6578 hH).trans (sound258 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix991 (2 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix991 (2 : Fin 3) = raw6596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix991 raw6596; decide +kernel
    rw [heq]
    exact (canonical6596 hH).trans (sound168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node991 + (injectiveMoment H (mergeFirst pivotMatrix991 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix991 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix991 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value991, value162, value168, value258, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation992 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -2, 3, -1], ![2, 3, -4, -1]]

theorem sound992 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node992 = Sparse.eval value992 (momentVector H) := by
  have heq : pivotMatrix992 = (fun u v => node992.transpose (pivotPermutation992 u) v) := by apply Matrix.ext; unfold pivotMatrix992 node992 pivotPermutation992; decide +kernel
  have hmoment : injectiveMoment H node992 = injectiveMoment H pivotMatrix992 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix992 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix992 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix992 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix992 (0 : Fin 3) = raw2152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix992 raw2152; decide +kernel
    rw [heq]
    exact (canonical2152 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix992 (1 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix992 (1 : Fin 3) = raw6579 := by apply Matrix.ext; unfold mergeFirst pivotMatrix992 raw6579; decide +kernel
    rw [heq]
    exact (canonical6579 hH).trans (sound241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix992 (2 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix992 (2 : Fin 3) = raw6597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix992 raw6597; decide +kernel
    rw [heq]
    exact (canonical6597 hH).trans (sound243 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node992 + (injectiveMoment H (mergeFirst pivotMatrix992 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix992 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix992 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value992, value241, value243, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation993 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix993 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, -2, 1, 1], ![2, 3, -3, -2]]

theorem sound993 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node993 = Sparse.eval value993 (momentVector H) := by
  have heq : pivotMatrix993 = (fun u v => node993.transpose (pivotPermutation993 u) v) := by apply Matrix.ext; unfold pivotMatrix993 node993 pivotPermutation993; decide +kernel
  have hmoment : injectiveMoment H node993 = injectiveMoment H pivotMatrix993 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix993 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix993 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix993 (0 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix993 (0 : Fin 3) = raw2532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix993 raw2532; decide +kernel
    rw [heq]
    exact (canonical2532 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix993 (1 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix993 (1 : Fin 3) = raw6900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix993 raw6900; decide +kernel
    rw [heq]
    exact (canonical6900 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix993 (2 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix993 (2 : Fin 3) = raw6915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix993 raw6915; decide +kernel
    rw [heq]
    exact (canonical6915 hH).trans (sound174 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node993 + (injectiveMoment H (mergeFirst pivotMatrix993 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix993 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix993 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value993, value167, value174, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation994 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix994 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4]]

theorem sound994 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node994 = Sparse.eval value994 (momentVector H) := by
  have heq : pivotMatrix994 = (fun u v => node994 (pivotPermutation994 u) v) := by apply Matrix.ext; unfold pivotMatrix994 node994 pivotPermutation994; decide +kernel
  have hmoment : injectiveMoment H node994 = injectiveMoment H pivotMatrix994 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix994 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix994 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix994 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix994 (0 : Fin 3) = raw8378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix994 raw8378; decide +kernel
    rw [heq]
    exact (canonical8378 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix994 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix994 (1 : Fin 3) = raw6561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix994 raw6561; decide +kernel
    rw [heq]
    exact (canonical6561 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix994 (2 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix994 (2 : Fin 3) = raw6386 := by apply Matrix.ext; unfold mergeFirst pivotMatrix994 raw6386; decide +kernel
    rw [heq]
    exact (canonical6386 hH).trans (sound127 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node994 + (injectiveMoment H (mergeFirst pivotMatrix994 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix994 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix994 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value994, value127, value153, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation995 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -1, 2, -1], ![2, 2, -3, -1]]

theorem sound995 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node995 = Sparse.eval value995 (momentVector H) := by
  have heq : pivotMatrix995 = (fun u v => node995.transpose (pivotPermutation995 u) v) := by apply Matrix.ext; unfold pivotMatrix995 node995 pivotPermutation995; decide +kernel
  have hmoment : injectiveMoment H node995 = injectiveMoment H pivotMatrix995 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix995 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix995 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix995 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix995 (0 : Fin 3) = raw2205 := by apply Matrix.ext; unfold mergeFirst pivotMatrix995 raw2205; decide +kernel
    rw [heq]
    exact (canonical2205 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix995 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix995 (1 : Fin 3) = raw6587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix995 raw6587; decide +kernel
    rw [heq]
    exact (canonical6587 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix995 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix995 (2 : Fin 3) = raw6627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix995 raw6627; decide +kernel
    rw [heq]
    exact (canonical6627 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node995 + (injectiveMoment H (mergeFirst pivotMatrix995 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix995 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix995 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value995, value175, value181, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation996 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix996 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, -1, 3, -2], ![2, 2, -4, 0]]

theorem sound996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node996 = Sparse.eval value996 (momentVector H) := by
  have heq : pivotMatrix996 = (fun u v => node996.transpose (pivotPermutation996 u) v) := by apply Matrix.ext; unfold pivotMatrix996 node996 pivotPermutation996; decide +kernel
  have hmoment : injectiveMoment H node996 = injectiveMoment H pivotMatrix996 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix996 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix996 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix996 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix996 (0 : Fin 3) = raw2206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix996 raw2206; decide +kernel
    rw [heq]
    exact (canonical2206 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix996 (1 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix996 (1 : Fin 3) = raw6588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix996 raw6588; decide +kernel
    rw [heq]
    exact (canonical6588 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix996 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix996 (2 : Fin 3) = raw6628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix996 raw6628; decide +kernel
    rw [heq]
    exact (canonical6628 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node996 + (injectiveMoment H (mergeFirst pivotMatrix996 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix996 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix996 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value996, value244, value246, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation997 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, -1, -2, 3], ![2, 2, 0, -4]]

theorem sound997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node997 = Sparse.eval value997 (momentVector H) := by
  have heq : pivotMatrix997 = (fun u v => node997.transpose (pivotPermutation997 u) v) := by apply Matrix.ext; unfold pivotMatrix997 node997 pivotPermutation997; decide +kernel
  have hmoment : injectiveMoment H node997 = injectiveMoment H pivotMatrix997 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix997 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix997 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix997 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix997 (0 : Fin 3) = raw2534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix997 raw2534; decide +kernel
    rw [heq]
    exact (canonical2534 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix997 (1 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix997 (1 : Fin 3) = raw6902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix997 raw6902; decide +kernel
    rw [heq]
    exact (canonical6902 hH).trans (sound218 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix997 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix997 (2 : Fin 3) = raw6920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix997 raw6920; decide +kernel
    rw [heq]
    exact (canonical6920 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node997 + (injectiveMoment H (mergeFirst pivotMatrix997 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix997 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix997 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value997, value215, value218, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation998 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix998 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4]]

theorem sound998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node998 = Sparse.eval value998 (momentVector H) := by
  have heq : pivotMatrix998 = (fun u v => node998 (pivotPermutation998 u) v) := by apply Matrix.ext; unfold pivotMatrix998 node998 pivotPermutation998; decide +kernel
  have hmoment : injectiveMoment H node998 = injectiveMoment H pivotMatrix998 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix998 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix998 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix998 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix998 (0 : Fin 3) = raw8311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix998 raw8311; decide +kernel
    rw [heq]
    exact (canonical8311 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix998 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix998 (1 : Fin 3) = raw6561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix998 raw6561; decide +kernel
    rw [heq]
    exact (canonical6561 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix998 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix998 (2 : Fin 3) = raw6397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix998 raw6397; decide +kernel
    rw [heq]
    exact (canonical6397 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node998 + (injectiveMoment H (mergeFirst pivotMatrix998 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix998 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix998 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value998, value150, value153, value35, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation999 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, -1, 3, -2], ![2, 2, -5, 1]]

theorem sound999 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node999 = Sparse.eval value999 (momentVector H) := by
  have heq : pivotMatrix999 = (fun u v => node999.transpose (pivotPermutation999 u) v) := by apply Matrix.ext; unfold pivotMatrix999 node999 pivotPermutation999; decide +kernel
  have hmoment : injectiveMoment H node999 = injectiveMoment H pivotMatrix999 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix999 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix999 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix999 (0 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix999 (0 : Fin 3) = raw2550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix999 raw2550; decide +kernel
    rw [heq]
    exact (canonical2550 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix999 (1 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix999 (1 : Fin 3) = raw6904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix999 raw6904; decide +kernel
    rw [heq]
    exact (canonical6904 hH).trans (sound124 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix999 (2 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix999 (2 : Fin 3) = raw6924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix999 raw6924; decide +kernel
    rw [heq]
    exact (canonical6924 hH).trans (sound127 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node999 + (injectiveMoment H (mergeFirst pivotMatrix999 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix999 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix999 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value999, value124, value127, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1000 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1000 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem sound1000 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1000 = Sparse.eval value1000 (momentVector H) := by
  have heq : pivotMatrix1000 = (fun u v => node1000 (pivotPermutation1000 u) v) := by apply Matrix.ext; unfold pivotMatrix1000 node1000 pivotPermutation1000; decide +kernel
  have hmoment : injectiveMoment H node1000 = injectiveMoment H pivotMatrix1000 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1000 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1000 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1000 (0 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1000 (0 : Fin 3) = raw5793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1000 raw5793; decide +kernel
    rw [heq]
    exact (canonical5793 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1000 (1 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1000 (1 : Fin 3) = raw6510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1000 raw6510; decide +kernel
    rw [heq]
    exact (canonical6510 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1000 (2 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1000 (2 : Fin 3) = raw6546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1000 raw6546; decide +kernel
    rw [heq]
    exact (canonical6546 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1000 + (injectiveMoment H (mergeFirst pivotMatrix1000 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1000 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1000 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1000, value207, value210, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1001 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1001 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, -3, 1], ![1, 0, 2, -3]]

theorem sound1001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1001 = Sparse.eval value1001 (momentVector H) := by
  have heq : pivotMatrix1001 = (fun u v => node1001 (pivotPermutation1001 u) v) := by apply Matrix.ext; unfold pivotMatrix1001 node1001 pivotPermutation1001; decide +kernel
  have hmoment : injectiveMoment H node1001 = injectiveMoment H pivotMatrix1001 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1001 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1001 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1001 (0 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1001 (0 : Fin 3) = raw5796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1001 raw5796; decide +kernel
    rw [heq]
    exact (canonical5796 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1001 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1001 (1 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1001 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1001 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1001 (2 : Fin 3) = raw6556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1001 raw6556; decide +kernel
    rw [heq]
    exact (canonical6556 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1001 + (injectiveMoment H (mergeFirst pivotMatrix1001 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1001 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1001 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1001, value107, value185, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1002 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1002 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound1002 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1002 = Sparse.eval value1002 (momentVector H) := by
  have heq : pivotMatrix1002 = (fun u v => node1002 (pivotPermutation1002 u) v) := by apply Matrix.ext; unfold pivotMatrix1002 node1002 pivotPermutation1002; decide +kernel
  have hmoment : injectiveMoment H node1002 = injectiveMoment H pivotMatrix1002 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1002 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1002 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1002 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1002 (0 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1002 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1002 (1 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1002 (1 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1002 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1002 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1002 (2 : Fin 3) = raw6557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1002 raw6557; decide +kernel
    rw [heq]
    exact (canonical6557 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1002 + (injectiveMoment H (mergeFirst pivotMatrix1002 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1002 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1002 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1002, value203, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1003 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1003 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem sound1003 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1003 = Sparse.eval value1003 (momentVector H) := by
  have heq : pivotMatrix1003 = (fun u v => node1003 (pivotPermutation1003 u) v) := by apply Matrix.ext; unfold pivotMatrix1003 node1003 pivotPermutation1003; decide +kernel
  have hmoment : injectiveMoment H node1003 = injectiveMoment H pivotMatrix1003 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1003 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1003 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1003 (0 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1003 (0 : Fin 3) = raw5800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1003 raw5800; decide +kernel
    rw [heq]
    exact (canonical5800 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1003 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1003 (1 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1003 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1003 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1003 (2 : Fin 3) = raw6559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1003 raw6559; decide +kernel
    rw [heq]
    exact (canonical6559 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1003 + (injectiveMoment H (mergeFirst pivotMatrix1003 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1003 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1003 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1003, value181, value185, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1004 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1004 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

theorem sound1004 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1004 = Sparse.eval value1004 (momentVector H) := by
  have heq : pivotMatrix1004 = (fun u v => node1004 (pivotPermutation1004 u) v) := by apply Matrix.ext; unfold pivotMatrix1004 node1004 pivotPermutation1004; decide +kernel
  have hmoment : injectiveMoment H node1004 = injectiveMoment H pivotMatrix1004 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1004 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1004 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1004 (0 : Fin 3)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1004 (0 : Fin 3) = raw5801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1004 raw5801; decide +kernel
    rw [heq]
    exact (canonical5801 hH).trans (sound102 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1004 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1004 (1 : Fin 3) = raw6555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1004 raw6555; decide +kernel
    rw [heq]
    exact (canonical6555 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1004 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1004 (2 : Fin 3) = raw6560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1004 raw6560; decide +kernel
    rw [heq]
    exact (canonical6560 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1004 + (injectiveMoment H (mergeFirst pivotMatrix1004 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1004 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1004 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1004, value102, value153, value155, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1005 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem sound1005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1005 = Sparse.eval value1005 (momentVector H) := by
  have heq : pivotMatrix1005 = (fun u v => node1005.transpose (pivotPermutation1005 u) v) := by apply Matrix.ext; unfold pivotMatrix1005 node1005 pivotPermutation1005; decide +kernel
  have hmoment : injectiveMoment H node1005 = injectiveMoment H pivotMatrix1005 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1005 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1005 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1005 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1005 (0 : Fin 3) = raw2488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1005 raw2488; decide +kernel
    rw [heq]
    exact (canonical2488 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1005 (1 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1005 (1 : Fin 3) = raw6591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1005 raw6591; decide +kernel
    rw [heq]
    exact (canonical6591 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1005 (2 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1005 (2 : Fin 3) = raw6706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1005 raw6706; decide +kernel
    rw [heq]
    exact (canonical6706 hH).trans (sound227 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1005 + (injectiveMoment H (mergeFirst pivotMatrix1005 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1005 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1005 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1005, value224, value227, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1006 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1006 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

theorem sound1006 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1006 = Sparse.eval value1006 (momentVector H) := by
  have heq : pivotMatrix1006 = (fun u v => node1006 (pivotPermutation1006 u) v) := by apply Matrix.ext; unfold pivotMatrix1006 node1006 pivotPermutation1006; decide +kernel
  have hmoment : injectiveMoment H node1006 = injectiveMoment H pivotMatrix1006 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1006 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1006 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1006 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1006 (0 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1006 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1006 (1 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1006 (1 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1006 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1006 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1006 (2 : Fin 3) = raw6418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1006 raw6418; decide +kernel
    rw [heq]
    exact (canonical6418 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1006 + (injectiveMoment H (mergeFirst pivotMatrix1006 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1006 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1006 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1006, value210, value230, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1007 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1007 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 2, -3, 1], ![2, -1, 1, -2]]

theorem sound1007 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1007 = Sparse.eval value1007 (momentVector H) := by
  have heq : pivotMatrix1007 = (fun u v => node1007.transpose (pivotPermutation1007 u) v) := by apply Matrix.ext; unfold pivotMatrix1007 node1007 pivotPermutation1007; decide +kernel
  have hmoment : injectiveMoment H node1007 = injectiveMoment H pivotMatrix1007 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1007 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1007 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1007 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1007 (0 : Fin 3) = raw2625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1007 raw2625; decide +kernel
    rw [heq]
    exact (canonical2625 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1007 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1007 (1 : Fin 3) = raw6905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1007 raw6905; decide +kernel
    rw [heq]
    exact (canonical6905 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1007 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1007 (2 : Fin 3) = raw6934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1007 raw6934; decide +kernel
    rw [heq]
    exact (canonical6934 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1007 + (injectiveMoment H (mergeFirst pivotMatrix1007 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1007 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1007 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1007, value111, value181, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1008 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1008 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0]]

theorem sound1008 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1008 = Sparse.eval value1008 (momentVector H) := by
  have heq : pivotMatrix1008 = (fun u v => node1008 (pivotPermutation1008 u) v) := by apply Matrix.ext; unfold pivotMatrix1008 node1008 pivotPermutation1008; decide +kernel
  have hmoment : injectiveMoment H node1008 = injectiveMoment H pivotMatrix1008 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1008 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1008 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1008 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1008 (0 : Fin 3) = raw8414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1008 raw8414; decide +kernel
    rw [heq]
    exact (canonical8414 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1008 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1008 (1 : Fin 3) = raw6563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1008 raw6563; decide +kernel
    rw [heq]
    exact (canonical6563 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1008 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1008 (2 : Fin 3) = raw6418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1008 raw6418; decide +kernel
    rw [heq]
    exact (canonical6418 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1008 + (injectiveMoment H (mergeFirst pivotMatrix1008 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1008 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1008 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1008, value203, value210, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1009 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1009 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1]]

theorem sound1009 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1009 = Sparse.eval value1009 (momentVector H) := by
  have heq : pivotMatrix1009 = (fun u v => node1009 (pivotPermutation1009 u) v) := by apply Matrix.ext; unfold pivotMatrix1009 node1009 pivotPermutation1009; decide +kernel
  have hmoment : injectiveMoment H node1009 = injectiveMoment H pivotMatrix1009 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1009 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1009 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1009 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (0 : Fin 3) = raw8316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw8316; decide +kernel
    rw [heq]
    exact (canonical8316 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1009 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (1 : Fin 3) = raw6562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw6562; decide +kernel
    rw [heq]
    exact (canonical6562 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1009 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (2 : Fin 3) = raw6418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw6418; decide +kernel
    rw [heq]
    exact (canonical6418 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1009 + (injectiveMoment H (mergeFirst pivotMatrix1009 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1009 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1009 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1009, value210, value230, value44, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1010 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![2, -1, -2, 1]]

theorem sound1010 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1010 = Sparse.eval value1010 (momentVector H) := by
  have heq : pivotMatrix1010 = (fun u v => node1010.transpose (pivotPermutation1010 u) v) := by apply Matrix.ext; unfold pivotMatrix1010 node1010 pivotPermutation1010; decide +kernel
  have hmoment : injectiveMoment H node1010 = injectiveMoment H pivotMatrix1010 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1010 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1010 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1010 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1010 (0 : Fin 3) = raw2632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1010 raw2632; decide +kernel
    rw [heq]
    exact (canonical2632 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1010 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1010 (1 : Fin 3) = raw6907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1010 raw6907; decide +kernel
    rw [heq]
    exact (canonical6907 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1010 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1010 (2 : Fin 3) = raw6935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1010 raw6935; decide +kernel
    rw [heq]
    exact (canonical6935 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1010 + (injectiveMoment H (mergeFirst pivotMatrix1010 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1010 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1010 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1010, value203, value210, value224, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1011 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 2, 1, -3], ![2, -1, -3, 2]]

theorem sound1011 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1011 = Sparse.eval value1011 (momentVector H) := by
  have heq : pivotMatrix1011 = (fun u v => node1011.transpose (pivotPermutation1011 u) v) := by apply Matrix.ext; unfold pivotMatrix1011 node1011 pivotPermutation1011; decide +kernel
  have hmoment : injectiveMoment H node1011 = injectiveMoment H pivotMatrix1011 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1011 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1011 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1011 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1011 (0 : Fin 3) = raw2636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1011 raw2636; decide +kernel
    rw [heq]
    exact (canonical2636 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1011 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1011 (1 : Fin 3) = raw6908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1011 raw6908; decide +kernel
    rw [heq]
    exact (canonical6908 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1011 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1011 (2 : Fin 3) = raw6936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1011 raw6936; decide +kernel
    rw [heq]
    exact (canonical6936 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1011 + (injectiveMoment H (mergeFirst pivotMatrix1011 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1011 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1011 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1011, value103, value184, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1012 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 3, -3, 0], ![2, -2, 2, -2]]

theorem sound1012 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1012 = Sparse.eval value1012 (momentVector H) := by
  have heq : pivotMatrix1012 = (fun u v => node1012.transpose (pivotPermutation1012 u) v) := by apply Matrix.ext; unfold pivotMatrix1012 node1012 pivotPermutation1012; decide +kernel
  have hmoment : injectiveMoment H node1012 = injectiveMoment H pivotMatrix1012 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1012 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1012 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1012 (0 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1012 (0 : Fin 3) = raw2505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1012 raw2505; decide +kernel
    rw [heq]
    exact (canonical2505 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1012 (1 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1012 (1 : Fin 3) = raw6593 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1012 raw6593; decide +kernel
    rw [heq]
    exact (canonical6593 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1012 (2 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1012 (2 : Fin 3) = raw6710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1012 raw6710; decide +kernel
    rw [heq]
    exact (canonical6710 hH).trans (sound259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1012 + (injectiveMoment H (mergeFirst pivotMatrix1012 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1012 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1012 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1012, value101, value259, value260, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1013 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 3, -2, -1], ![2, -2, 1, -1]]

theorem sound1013 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1013 = Sparse.eval value1013 (momentVector H) := by
  have heq : pivotMatrix1013 = (fun u v => node1013.transpose (pivotPermutation1013 u) v) := by apply Matrix.ext; unfold pivotMatrix1013 node1013 pivotPermutation1013; decide +kernel
  have hmoment : injectiveMoment H node1013 = injectiveMoment H pivotMatrix1013 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1013 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1013 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1013 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1013 (0 : Fin 3) = raw2506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1013 raw2506; decide +kernel
    rw [heq]
    exact (canonical2506 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1013 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1013 (1 : Fin 3) = raw6594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1013 raw6594; decide +kernel
    rw [heq]
    exact (canonical6594 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1013 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1013 (2 : Fin 3) = raw6711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1013 raw6711; decide +kernel
    rw [heq]
    exact (canonical6711 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1013 + (injectiveMoment H (mergeFirst pivotMatrix1013 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1013 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1013 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1013, value111, value181, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1014 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 3, -4, 1], ![2, -2, 2, -2]]

theorem sound1014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1014 = Sparse.eval value1014 (momentVector H) := by
  have heq : pivotMatrix1014 = (fun u v => node1014.transpose (pivotPermutation1014 u) v) := by apply Matrix.ext; unfold pivotMatrix1014 node1014 pivotPermutation1014; decide +kernel
  have hmoment : injectiveMoment H node1014 = injectiveMoment H pivotMatrix1014 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1014 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1014 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1014 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1014 (0 : Fin 3) = raw2637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1014 raw2637; decide +kernel
    rw [heq]
    exact (canonical2637 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1014 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1014 (1 : Fin 3) = raw6909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1014 raw6909; decide +kernel
    rw [heq]
    exact (canonical6909 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1014 (2 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1014 (2 : Fin 3) = raw6937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1014 raw6937; decide +kernel
    rw [heq]
    exact (canonical6937 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1014 + (injectiveMoment H (mergeFirst pivotMatrix1014 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1014 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1014 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1014, value135, value149, value152, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1015 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1015 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1]]

theorem sound1015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1015 = Sparse.eval value1015 (momentVector H) := by
  have heq : pivotMatrix1015 = (fun u v => node1015 (pivotPermutation1015 u) v) := by apply Matrix.ext; unfold pivotMatrix1015 node1015 pivotPermutation1015; decide +kernel
  have hmoment : injectiveMoment H node1015 = injectiveMoment H pivotMatrix1015 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1015 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1015 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1015 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1015 (0 : Fin 3) = raw8417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1015 raw8417; decide +kernel
    rw [heq]
    exact (canonical8417 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1015 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1015 (1 : Fin 3) = raw6564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1015 raw6564; decide +kernel
    rw [heq]
    exact (canonical6564 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1015 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1015 (2 : Fin 3) = raw6419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1015 raw6419; decide +kernel
    rw [heq]
    exact (canonical6419 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1015 + (injectiveMoment H (mergeFirst pivotMatrix1015 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1015 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1015 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1015, value187, value215, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1016 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 3, -1, -2], ![2, -2, -1, 1]]

theorem sound1016 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1016 = Sparse.eval value1016 (momentVector H) := by
  have heq : pivotMatrix1016 = (fun u v => node1016.transpose (pivotPermutation1016 u) v) := by apply Matrix.ext; unfold pivotMatrix1016 node1016 pivotPermutation1016; decide +kernel
  have hmoment : injectiveMoment H node1016 = injectiveMoment H pivotMatrix1016 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1016 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1016 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1016 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1016 (0 : Fin 3) = raw2638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1016 raw2638; decide +kernel
    rw [heq]
    exact (canonical2638 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1016 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1016 (1 : Fin 3) = raw6910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1016 raw6910; decide +kernel
    rw [heq]
    exact (canonical6910 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1016 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1016 (2 : Fin 3) = raw6938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1016 raw6938; decide +kernel
    rw [heq]
    exact (canonical6938 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1016 + (injectiveMoment H (mergeFirst pivotMatrix1016 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1016 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1016 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1016, value111, value226, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1017 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1017 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 3, 0, -3], ![2, -2, -2, 2]]

theorem sound1017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1017 = Sparse.eval value1017 (momentVector H) := by
  have heq : pivotMatrix1017 = (fun u v => node1017.transpose (pivotPermutation1017 u) v) := by apply Matrix.ext; unfold pivotMatrix1017 node1017 pivotPermutation1017; decide +kernel
  have hmoment : injectiveMoment H node1017 = injectiveMoment H pivotMatrix1017 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1017 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1017 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1017 (0 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1017 (0 : Fin 3) = raw2639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1017 raw2639; decide +kernel
    rw [heq]
    exact (canonical2639 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1017 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1017 (1 : Fin 3) = raw6911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1017 raw6911; decide +kernel
    rw [heq]
    exact (canonical6911 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1017 (2 : Fin 3)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1017 (2 : Fin 3) = raw6939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1017 raw6939; decide +kernel
    rw [heq]
    exact (canonical6939 hH).trans (sound214 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1017 + (injectiveMoment H (mergeFirst pivotMatrix1017 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1017 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1017 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1017, value101, value212, value214, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1018 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 3, -1], ![0, 3, -2, -1], ![2, -2, -1, 1]]

theorem sound1018 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1018 = Sparse.eval value1018 (momentVector H) := by
  have heq : pivotMatrix1018 = (fun u v => node1018.transpose (pivotPermutation1018 u) v) := by apply Matrix.ext; unfold pivotMatrix1018 node1018 pivotPermutation1018; decide +kernel
  have hmoment : injectiveMoment H node1018 = injectiveMoment H pivotMatrix1018 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1018 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1018 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1018 (0 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1018 (0 : Fin 3) = raw2870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1018 raw2870; decide +kernel
    rw [heq]
    exact (canonical2870 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1018 (1 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1018 (1 : Fin 3) = raw6961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1018 raw6961; decide +kernel
    rw [heq]
    exact (canonical6961 hH).trans (sound109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1018 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1018 (2 : Fin 3) = raw6969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1018 raw6969; decide +kernel
    rw [heq]
    exact (canonical6969 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1018 + (injectiveMoment H (mergeFirst pivotMatrix1018 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1018 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1018 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1018, value107, value109, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1019 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![0, 4, -3, -1], ![2, -3, 2, -1]]

theorem sound1019 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1019 = Sparse.eval value1019 (momentVector H) := by
  have heq : pivotMatrix1019 = (fun u v => node1019.transpose (pivotPermutation1019 u) v) := by apply Matrix.ext; unfold pivotMatrix1019 node1019 pivotPermutation1019; decide +kernel
  have hmoment : injectiveMoment H node1019 = injectiveMoment H pivotMatrix1019 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1019 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1019 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1019 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1019 (0 : Fin 3) = raw2507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1019 raw2507; decide +kernel
    rw [heq]
    exact (canonical2507 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1019 (1 : Fin 3)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1019 (1 : Fin 3) = raw6595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1019 raw6595; decide +kernel
    rw [heq]
    exact (canonical6595 hH).trans (sound245 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1019 (2 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1019 (2 : Fin 3) = raw6712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1019 raw6712; decide +kernel
    rw [heq]
    exact (canonical6712 hH).trans (sound243 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1019 + (injectiveMoment H (mergeFirst pivotMatrix1019 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1019 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1019 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1019, value191, value243, value245, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1020 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![0, 4, -1, -3], ![2, -3, -1, 2]]

theorem sound1020 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1020 = Sparse.eval value1020 (momentVector H) := by
  have heq : pivotMatrix1020 = (fun u v => node1020.transpose (pivotPermutation1020 u) v) := by apply Matrix.ext; unfold pivotMatrix1020 node1020 pivotPermutation1020; decide +kernel
  have hmoment : injectiveMoment H node1020 = injectiveMoment H pivotMatrix1020 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1020 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1020 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1020 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1020 (0 : Fin 3) = raw2640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1020 raw2640; decide +kernel
    rw [heq]
    exact (canonical2640 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1020 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1020 (1 : Fin 3) = raw6912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1020 raw6912; decide +kernel
    rw [heq]
    exact (canonical6912 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1020 (2 : Fin 3)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1020 (2 : Fin 3) = raw6940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1020 raw6940; decide +kernel
    rw [heq]
    exact (canonical6940 hH).trans (sound221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1020 + (injectiveMoment H (mergeFirst pivotMatrix1020 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1020 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1020 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1020, value191, value221, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1021 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -3, 3, 0], ![2, 3, -3, -2]]

theorem sound1021 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1021 = Sparse.eval value1021 (momentVector H) := by
  have heq : pivotMatrix1021 = (fun u v => node1021.transpose (pivotPermutation1021 u) v) := by apply Matrix.ext; unfold pivotMatrix1021 node1021 pivotPermutation1021; decide +kernel
  have hmoment : injectiveMoment H node1021 = injectiveMoment H pivotMatrix1021 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1021 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1021 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1021 (0 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1021 (0 : Fin 3) = raw3292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1021 raw3292; decide +kernel
    rw [heq]
    exact (canonical3292 hH).trans (sound192 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1021 (1 : Fin 3)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1021 (1 : Fin 3) = raw7255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1021 raw7255; decide +kernel
    rw [heq]
    exact (canonical7255 hH).trans (sound277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1021 (2 : Fin 3)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1021 (2 : Fin 3) = raw7276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1021 raw7276; decide +kernel
    rw [heq]
    exact (canonical7276 hH).trans (sound289 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1021 + (injectiveMoment H (mergeFirst pivotMatrix1021 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1021 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1021 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1021, value192, value277, value289, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1022 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -3, 4, -1], ![2, 3, -4, -1]]

theorem sound1022 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1022 = Sparse.eval value1022 (momentVector H) := by
  have heq : pivotMatrix1022 = (fun u v => node1022.transpose (pivotPermutation1022 u) v) := by apply Matrix.ext; unfold pivotMatrix1022 node1022 pivotPermutation1022; decide +kernel
  have hmoment : injectiveMoment H node1022 = injectiveMoment H pivotMatrix1022 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1022 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1022 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1022 (0 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1022 (0 : Fin 3) = raw3293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1022 raw3293; decide +kernel
    rw [heq]
    exact (canonical3293 hH).trans (sound193 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1022 (1 : Fin 3)) =
      Sparse.eval value278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1022 (1 : Fin 3) = raw7256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1022 raw7256; decide +kernel
    rw [heq]
    exact (canonical7256 hH).trans (sound278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1022 (2 : Fin 3)) =
      Sparse.eval value290 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1022 (2 : Fin 3) = raw7277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1022 raw7277; decide +kernel
    rw [heq]
    exact (canonical7277 hH).trans (sound290 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1022 + (injectiveMoment H (mergeFirst pivotMatrix1022 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1022 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1022 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1022, value193, value278, value290, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1023 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1023 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, 0, 2], ![0, 0, -3, 3], ![1, 0, 3, -4]]

theorem sound1023 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1023 = Sparse.eval value1023 (momentVector H) := by
  have heq : pivotMatrix1023 = (fun u v => node1023 (pivotPermutation1023 u) v) := by apply Matrix.ext; unfold pivotMatrix1023 node1023 pivotPermutation1023; decide +kernel
  have hmoment : injectiveMoment H node1023 = injectiveMoment H pivotMatrix1023 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1023 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1023 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1023 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1023 (0 : Fin 3) = raw7329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1023 raw7329; decide +kernel
    rw [heq]
    exact (canonical7329 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1023 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1023 (1 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1023 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1023 (2 : Fin 3)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1023 (2 : Fin 3) = raw6420 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1023 raw6420; decide +kernel
    rw [heq]
    exact (canonical6420 hH).trans (sound129 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1023 + (injectiveMoment H (mergeFirst pivotMatrix1023 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1023 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1023 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1023, value129, value155, value53, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
