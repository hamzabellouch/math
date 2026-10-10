import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical274

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation256 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix256 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 2, -2]]

theorem sound256 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node256 = Sparse.eval value256 (momentVector H) := by
  have heq : pivotMatrix256 = (fun u v => node256 (pivotPermutation256 u) v) := by apply Matrix.ext; unfold pivotMatrix256 node256 pivotPermutation256; decide +kernel
  have hmoment : injectiveMoment H node256 = injectiveMoment H pivotMatrix256 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix256 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix256 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix256 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (0 : Fin 3) = raw7987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw7987; decide +kernel
    rw [heq]
    exact (canonical7987 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix256 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (1 : Fin 3) = raw5555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw5555; decide +kernel
    rw [heq]
    exact (canonical5555 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix256 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (2 : Fin 3) = raw5547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw5547; decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node256 + (injectiveMoment H (mergeFirst pivotMatrix256 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix256 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix256 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value256, value52, value9, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation257 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix257 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 2, 3, -2], ![4, -2, -3, 1]]

theorem sound257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node257 = Sparse.eval value257 (momentVector H) := by
  have heq : pivotMatrix257 = (fun u v => node257.transpose (pivotPermutation257 u) v) := by apply Matrix.ext; unfold pivotMatrix257 node257 pivotPermutation257; decide +kernel
  have hmoment : injectiveMoment H node257 = injectiveMoment H pivotMatrix257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix257 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix257 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix257 (0 : Fin 2)) =
      Sparse.eval value15 (momentVector H) := by
    have heq : mergeFirst pivotMatrix257 (0 : Fin 2) = raw181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix257 raw181; decide +kernel
    rw [heq]
    exact (canonical181 hH).trans (sound15 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix257 (1 : Fin 2)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix257 (1 : Fin 2) = raw843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix257 raw843; decide +kernel
    rw [heq]
    exact (canonical843 hH).trans (sound23 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node257 + (injectiveMoment H (mergeFirst pivotMatrix257 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix257 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value257, value15, value23, Sparse.eval] at hc ⊢
  linarith

theorem sound258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node258 = Sparse.eval value258 (momentVector H) := by
  have hc : momentVector H 236 = injectiveMoment H node258 := rfl
  simp [value258, Sparse.eval, hc]

def pivotPermutation259 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix259 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 2, -3]]

theorem sound259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node259 = Sparse.eval value259 (momentVector H) := by
  have heq : pivotMatrix259 = (fun u v => node259 (pivotPermutation259 u) v) := by apply Matrix.ext; unfold pivotMatrix259 node259 pivotPermutation259; decide +kernel
  have hmoment : injectiveMoment H node259 = injectiveMoment H pivotMatrix259 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix259 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix259 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix259 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix259 (0 : Fin 3) = raw2861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix259 raw2861; decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix259 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix259 (1 : Fin 3) = raw5949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix259 raw5949; decide +kernel
    rw [heq]
    exact (canonical5949 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix259 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix259 (2 : Fin 3) = raw5989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix259 raw5989; decide +kernel
    rw [heq]
    exact (canonical5989 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node259 + (injectiveMoment H (mergeFirst pivotMatrix259 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix259 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix259 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value259, value10, value58, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node260 = Sparse.eval value260 (momentVector H) := by
  have hc : momentVector H 237 = injectiveMoment H node260 := rfl
  simp [value260, Sparse.eval, hc]

def pivotPermutation261 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix261 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, 2, -1], ![1, 1, -2]]

theorem sound261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node261 = Sparse.eval value261 (momentVector H) := by
  have heq : pivotMatrix261 = (fun u v => node261 (pivotPermutation261 u) v) := by apply Matrix.ext; unfold pivotMatrix261 node261 pivotPermutation261; decide +kernel
  have hmoment : injectiveMoment H node261 = injectiveMoment H pivotMatrix261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix261 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix261 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (0 : Fin 3) = raw7995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw7995; decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (2 : Fin 3) = raw5891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5891; decide +kernel
    rw [heq]
    exact (canonical5891 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node261 + (injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value261, value36, value56, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node262 = Sparse.eval value262 (momentVector H) := by
  have hc : momentVector H 238 = injectiveMoment H node262 := rfl
  simp [value262, Sparse.eval, hc]

def pivotPermutation263 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix263 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2], ![1, 0, -1]]

theorem sound263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node263 = Sparse.eval value263 (momentVector H) := by
  have heq : pivotMatrix263 = (fun u v => node263 (pivotPermutation263 u) v) := by apply Matrix.ext; unfold pivotMatrix263 node263 pivotPermutation263; decide +kernel
  have hmoment : injectiveMoment H node263 = injectiveMoment H pivotMatrix263 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix263 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix263 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix263 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (0 : Fin 3) = raw7996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw7996; decide +kernel
    rw [heq]
    exact (canonical7996 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix263 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix263 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (2 : Fin 3) = raw5902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw5902; decide +kernel
    rw [heq]
    exact (canonical5902 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node263 + (injectiveMoment H (mergeFirst pivotMatrix263 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix263 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix263 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value263, value43, value57, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation264 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix264 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 2, 2], ![3, 2, -2, -3]]

theorem sound264 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node264 = Sparse.eval value264 (momentVector H) := by
  have heq : pivotMatrix264 = (fun u v => node264.transpose (pivotPermutation264 u) v) := by apply Matrix.ext; unfold pivotMatrix264 node264 pivotPermutation264; decide +kernel
  have hmoment : injectiveMoment H node264 = injectiveMoment H pivotMatrix264 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix264 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix264 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix264 (0 : Fin 2)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix264 (0 : Fin 2) = raw217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix264 raw217; decide +kernel
    rw [heq]
    exact (canonical217 hH).trans (sound23 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix264 (1 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix264 (1 : Fin 2) = raw1332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix264 raw1332; decide +kernel
    rw [heq]
    exact (canonical1332 hH).trans (sound45 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node264 + (injectiveMoment H (mergeFirst pivotMatrix264 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix264 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value264, value23, value45, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation265 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix265 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -2, 3, 1], ![3, 2, -3, -2]]

theorem sound265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node265 = Sparse.eval value265 (momentVector H) := by
  have heq : pivotMatrix265 = (fun u v => node265.transpose (pivotPermutation265 u) v) := by apply Matrix.ext; unfold pivotMatrix265 node265 pivotPermutation265; decide +kernel
  have hmoment : injectiveMoment H node265 = injectiveMoment H pivotMatrix265 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix265 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix265 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix265 (0 : Fin 2)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix265 (0 : Fin 2) = raw218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix265 raw218; decide +kernel
    rw [heq]
    exact (canonical218 hH).trans (sound23 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix265 (1 : Fin 2)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix265 (1 : Fin 2) = raw1337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix265 raw1337; decide +kernel
    rw [heq]
    exact (canonical1337 hH).trans (sound25 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node265 + (injectiveMoment H (mergeFirst pivotMatrix265 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix265 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value265, value23, value25, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation266 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix266 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![0, -2, 2], ![0, 4, -4]]

theorem sound266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node266 = Sparse.eval value266 (momentVector H) := by
  have heq : pivotMatrix266 = (fun u v => node266 (pivotPermutation266 u) v) := by apply Matrix.ext; unfold pivotMatrix266 node266 pivotPermutation266; decide +kernel
  have hmoment : injectiveMoment H node266 = injectiveMoment H pivotMatrix266 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix266 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix266 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix266 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix266 (0 : Fin 3) = raw8171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix266 raw8171; decide +kernel
    rw [heq]
    exact (canonical8171 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix266 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix266 (1 : Fin 3) = raw5988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix266 raw5988; decide +kernel
    rw [heq]
    exact (canonical5988 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix266 (2 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix266 (2 : Fin 3) = raw5916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix266 raw5916; decide +kernel
    rw [heq]
    exact (canonical5916 hH).trans (sound48 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node266 + (injectiveMoment H (mergeFirst pivotMatrix266 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix266 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix266 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value266, value48, value59, value9, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation267 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix267 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3]]

theorem sound267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node267 = Sparse.eval value267 (momentVector H) := by
  have heq : pivotMatrix267 = (fun u v => node267 (pivotPermutation267 u) v) := by apply Matrix.ext; unfold pivotMatrix267 node267 pivotPermutation267; decide +kernel
  have hmoment : injectiveMoment H node267 = injectiveMoment H pivotMatrix267 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix267 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix267 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix267 (0 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix267 (0 : Fin 3) = raw5540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix267 raw5540; decide +kernel
    rw [heq]
    exact (canonical5540 hH).trans (sound51 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix267 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix267 (1 : Fin 3) = raw5949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix267 raw5949; decide +kernel
    rw [heq]
    exact (canonical5949 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix267 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix267 (2 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix267 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node267 + (injectiveMoment H (mergeFirst pivotMatrix267 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix267 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix267 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value267, value10, value51, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation268 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix268 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2]]

theorem sound268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node268 = Sparse.eval value268 (momentVector H) := by
  have heq : pivotMatrix268 = (fun u v => node268 (pivotPermutation268 u) v) := by apply Matrix.ext; unfold pivotMatrix268 node268 pivotPermutation268; decide +kernel
  have hmoment : injectiveMoment H node268 = injectiveMoment H pivotMatrix268 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix268 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix268 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix268 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (0 : Fin 3) = raw5547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5547; decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix268 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix268 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node268 + (injectiveMoment H (mergeFirst pivotMatrix268 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix268 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix268 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value268, value52, value56, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation269 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix269 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1]]

theorem sound269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node269 = Sparse.eval value269 (momentVector H) := by
  have heq : pivotMatrix269 = (fun u v => node269 (pivotPermutation269 u) v) := by apply Matrix.ext; unfold pivotMatrix269 node269 pivotPermutation269; decide +kernel
  have hmoment : injectiveMoment H node269 = injectiveMoment H pivotMatrix269 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix269 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix269 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix269 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (0 : Fin 3) = raw5550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5550; decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix269 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix269 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (2 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node269 + (injectiveMoment H (mergeFirst pivotMatrix269 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix269 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix269 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value269, value53, value57, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation270 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix270 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0]]

theorem sound270 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node270 = Sparse.eval value270 (momentVector H) := by
  have heq : pivotMatrix270 = (fun u v => node270 (pivotPermutation270 u) v) := by apply Matrix.ext; unfold pivotMatrix270 node270 pivotPermutation270; decide +kernel
  have hmoment : injectiveMoment H node270 = injectiveMoment H pivotMatrix270 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix270 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix270 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix270 (0 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix270 (0 : Fin 3) = raw5552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix270 raw5552; decide +kernel
    rw [heq]
    exact (canonical5552 hH).trans (sound54 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix270 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix270 (1 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix270 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix270 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix270 (2 : Fin 3) = raw5986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix270 raw5986; decide +kernel
    rw [heq]
    exact (canonical5986 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node270 + (injectiveMoment H (mergeFirst pivotMatrix270 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix270 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix270 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value270, value54, value58, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation271 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix271 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1]]

theorem sound271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node271 = Sparse.eval value271 (momentVector H) := by
  have heq : pivotMatrix271 = (fun u v => node271 (pivotPermutation271 u) v) := by apply Matrix.ext; unfold pivotMatrix271 node271 pivotPermutation271; decide +kernel
  have hmoment : injectiveMoment H node271 = injectiveMoment H pivotMatrix271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix271 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix271 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (2 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node271 + (injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value271, value56, value57, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation272 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix272 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0]]

theorem sound272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node272 = Sparse.eval value272 (momentVector H) := by
  have heq : pivotMatrix272 = (fun u v => node272 (pivotPermutation272 u) v) := by apply Matrix.ext; unfold pivotMatrix272 node272 pivotPermutation272; decide +kernel
  have hmoment : injectiveMoment H node272 = injectiveMoment H pivotMatrix272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix272 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix272 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (1 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node272 + (injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value272, value57, value58, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation273 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix273 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 3, -3], ![1, -2, 1]]

theorem sound273 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node273 = Sparse.eval value273 (momentVector H) := by
  have heq : pivotMatrix273 = (fun u v => node273 (pivotPermutation273 u) v) := by apply Matrix.ext; unfold pivotMatrix273 node273 pivotPermutation273; decide +kernel
  have hmoment : injectiveMoment H node273 = injectiveMoment H pivotMatrix273 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix273 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix273 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix273 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix273 (0 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix273 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix273 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix273 (1 : Fin 3) = raw5986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix273 raw5986; decide +kernel
    rw [heq]
    exact (canonical5986 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix273 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix273 (2 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix273 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node273 + (injectiveMoment H (mergeFirst pivotMatrix273 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix273 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix273 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value273, value58, value59, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation274 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix274 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 2, 2, -2], ![3, -2, -2, 1]]

theorem sound274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node274 = Sparse.eval value274 (momentVector H) := by
  have heq : pivotMatrix274 = (fun u v => node274.transpose (pivotPermutation274 u) v) := by apply Matrix.ext; unfold pivotMatrix274 node274 pivotPermutation274; decide +kernel
  have hmoment : injectiveMoment H node274 = injectiveMoment H pivotMatrix274 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix274 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix274 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix274 (0 : Fin 2)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix274 (0 : Fin 2) = raw842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix274 raw842; decide +kernel
    rw [heq]
    exact (canonical842 hH).trans (sound25 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix274 (1 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix274 (1 : Fin 2) = raw5453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix274 raw5453; decide +kernel
    rw [heq]
    exact (canonical5453 hH).trans (sound45 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node274 + (injectiveMoment H (mergeFirst pivotMatrix274 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix274 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value274, value25, value45, Sparse.eval] at hc ⊢
  linarith

theorem sound275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node275 = Sparse.eval value275 (momentVector H) := by
  have hc : momentVector H 30 = injectiveMoment H node275 := rfl
  simp [value275, Sparse.eval, hc]

theorem sound276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node276 = Sparse.eval value276 (momentVector H) := by
  have hc : momentVector H 31 = injectiveMoment H node276 := rfl
  simp [value276, Sparse.eval, hc]

def pivotPermutation277 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix277 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -3, 3, 1], ![2, 3, -3, -2]]

theorem sound277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node277 = Sparse.eval value277 (momentVector H) := by
  have heq : pivotMatrix277 = (fun u v => node277.transpose (pivotPermutation277 u) v) := by apply Matrix.ext; unfold pivotMatrix277 node277 pivotPermutation277; decide +kernel
  have hmoment : injectiveMoment H node277 = injectiveMoment H pivotMatrix277 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix277 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix277 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix277 (0 : Fin 2)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix277 (0 : Fin 2) = raw930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix277 raw930; decide +kernel
    rw [heq]
    exact (canonical930 hH).trans (sound23 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix277 (1 : Fin 2)) =
      Sparse.eval value24 (momentVector H) := by
    have heq : mergeFirst pivotMatrix277 (1 : Fin 2) = raw5488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix277 raw5488; decide +kernel
    rw [heq]
    exact (canonical5488 hH).trans (sound24 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node277 + (injectiveMoment H (mergeFirst pivotMatrix277 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix277 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value277, value23, value24, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation278 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix278 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -3, 3], ![0, 4, -4]]

theorem sound278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node278 = Sparse.eval value278 (momentVector H) := by
  have heq : pivotMatrix278 = (fun u v => node278 (pivotPermutation278 u) v) := by apply Matrix.ext; unfold pivotMatrix278 node278 pivotPermutation278; decide +kernel
  have hmoment : injectiveMoment H node278 = injectiveMoment H pivotMatrix278 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix278 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix278 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix278 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix278 (0 : Fin 3) = raw8548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix278 raw8548; decide +kernel
    rw [heq]
    exact (canonical8548 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix278 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix278 (1 : Fin 3) = raw6877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix278 raw6877; decide +kernel
    rw [heq]
    exact (canonical6877 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix278 (2 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix278 (2 : Fin 3) = raw6773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix278 raw6773; decide +kernel
    rw [heq]
    exact (canonical6773 hH).trans (sound49 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node278 + (injectiveMoment H (mergeFirst pivotMatrix278 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix278 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix278 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value278, value49, value59, value8, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation279 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix279 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![2, 2, -2, -2]]

theorem sound279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node279 = Sparse.eval value279 (momentVector H) := by
  have heq : pivotMatrix279 = (fun u v => node279.transpose (pivotPermutation279 u) v) := by apply Matrix.ext; unfold pivotMatrix279 node279 pivotPermutation279; decide +kernel
  have hmoment : injectiveMoment H node279 = injectiveMoment H pivotMatrix279 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix279 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix279 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (0 : Fin 2) = raw1332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw1332; decide +kernel
    rw [heq]
    exact (canonical1332 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (1 : Fin 2) = raw5848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw5848; decide +kernel
    rw [heq]
    exact (canonical5848 hH).trans (sound46 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node279 + (injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value279, value45, value46, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation280 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix280 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3]]

theorem sound280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node280 = Sparse.eval value280 (momentVector H) := by
  have heq : pivotMatrix280 = (fun u v => node280 (pivotPermutation280 u) v) := by apply Matrix.ext; unfold pivotMatrix280 node280 pivotPermutation280; decide +kernel
  have hmoment : injectiveMoment H node280 = injectiveMoment H pivotMatrix280 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix280 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix280 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix280 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (0 : Fin 3) = raw8560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw8560; decide +kernel
    rw [heq]
    exact (canonical8560 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix280 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (1 : Fin 3) = raw6880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw6880; decide +kernel
    rw [heq]
    exact (canonical6880 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix280 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (2 : Fin 3) = raw6789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw6789; decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node280 + (injectiveMoment H (mergeFirst pivotMatrix280 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix280 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix280 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value280, value10, value52, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation281 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix281 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 4, -4]]

theorem sound281 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node281 = Sparse.eval value281 (momentVector H) := by
  have heq : pivotMatrix281 = (fun u v => node281 (pivotPermutation281 u) v) := by apply Matrix.ext; unfold pivotMatrix281 node281 pivotPermutation281; decide +kernel
  have hmoment : injectiveMoment H node281 = injectiveMoment H pivotMatrix281 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix281 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix281 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix281 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (0 : Fin 3) = raw8171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw8171; decide +kernel
    rw [heq]
    exact (canonical8171 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix281 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (1 : Fin 3) = raw6877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw6877; decide +kernel
    rw [heq]
    exact (canonical6877 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix281 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (2 : Fin 3) = raw6789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw6789; decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node281 + (injectiveMoment H (mergeFirst pivotMatrix281 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix281 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix281 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value281, value52, value59, value9, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation282 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix282 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 5, -2], ![2, 2, -5, 1]]

theorem sound282 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node282 = Sparse.eval value282 (momentVector H) := by
  have heq : pivotMatrix282 = (fun u v => node282.transpose (pivotPermutation282 u) v) := by apply Matrix.ext; unfold pivotMatrix282 node282 pivotPermutation282; decide +kernel
  have hmoment : injectiveMoment H node282 = injectiveMoment H pivotMatrix282 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix282 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix282 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix282 (0 : Fin 2)) =
      Sparse.eval value13 (momentVector H) := by
    have heq : mergeFirst pivotMatrix282 (0 : Fin 2) = raw1453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix282 raw1453; decide +kernel
    rw [heq]
    exact (canonical1453 hH).trans (sound13 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix282 (1 : Fin 2)) =
      Sparse.eval value13 (momentVector H) := by
    have heq : mergeFirst pivotMatrix282 (1 : Fin 2) = raw5998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix282 raw5998; decide +kernel
    rw [heq]
    exact (canonical5998 hH).trans (sound13 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node282 + (injectiveMoment H (mergeFirst pivotMatrix282 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix282 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value282, value13, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation283 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix283 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2]]

theorem sound283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node283 = Sparse.eval value283 (momentVector H) := by
  have heq : pivotMatrix283 = (fun u v => node283 (pivotPermutation283 u) v) := by apply Matrix.ext; unfold pivotMatrix283 node283 pivotPermutation283; decide +kernel
  have hmoment : injectiveMoment H node283 = injectiveMoment H pivotMatrix283 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix283 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix283 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix283 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix283 (0 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix283 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix283 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix283 (1 : Fin 3) = raw6832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix283 raw6832; decide +kernel
    rw [heq]
    exact (canonical6832 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix283 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix283 (2 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix283 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node283 + (injectiveMoment H (mergeFirst pivotMatrix283 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix283 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix283 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value283, value11, value56, value61, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation284 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix284 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1]]

theorem sound284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node284 = Sparse.eval value284 (momentVector H) := by
  have heq : pivotMatrix284 = (fun u v => node284 (pivotPermutation284 u) v) := by apply Matrix.ext; unfold pivotMatrix284 node284 pivotPermutation284; decide +kernel
  have hmoment : injectiveMoment H node284 = injectiveMoment H pivotMatrix284 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix284 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix284 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix284 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix284 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (1 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix284 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (2 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node284 + (injectiveMoment H (mergeFirst pivotMatrix284 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix284 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix284 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value284, value57, value61, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation285 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix285 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0]]

theorem sound285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node285 = Sparse.eval value285 (momentVector H) := by
  have heq : pivotMatrix285 = (fun u v => node285 (pivotPermutation285 u) v) := by apply Matrix.ext; unfold pivotMatrix285 node285 pivotPermutation285; decide +kernel
  have hmoment : injectiveMoment H node285 = injectiveMoment H pivotMatrix285 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix285 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix285 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix285 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (0 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix285 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix285 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (2 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node285 + (injectiveMoment H (mergeFirst pivotMatrix285 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix285 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix285 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value285, value58, value62, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation286 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix286 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1]]

theorem sound286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node286 = Sparse.eval value286 (momentVector H) := by
  have heq : pivotMatrix286 = (fun u v => node286 (pivotPermutation286 u) v) := by apply Matrix.ext; unfold pivotMatrix286 node286 pivotPermutation286; decide +kernel
  have hmoment : injectiveMoment H node286 = injectiveMoment H pivotMatrix286 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix286 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix286 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix286 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix286 (0 : Fin 3) = raw5986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix286 raw5986; decide +kernel
    rw [heq]
    exact (canonical5986 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix286 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix286 (1 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix286 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix286 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix286 (2 : Fin 3) = raw6875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix286 raw6875; decide +kernel
    rw [heq]
    exact (canonical6875 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node286 + (injectiveMoment H (mergeFirst pivotMatrix286 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix286 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix286 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value286, value59, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation287 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix287 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0]]

theorem sound287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node287 = Sparse.eval value287 (momentVector H) := by
  have heq : pivotMatrix287 = (fun u v => node287 (pivotPermutation287 u) v) := by apply Matrix.ext; unfold pivotMatrix287 node287 pivotPermutation287; decide +kernel
  have hmoment : injectiveMoment H node287 = injectiveMoment H pivotMatrix287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix287 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix287 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (0 : Fin 3) = raw7453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw7453; decide +kernel
    rw [heq]
    exact (canonical7453 hH).trans (sound64 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (2 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node287 + (injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value287, value61, value62, value64, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation288 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix288 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1]]

theorem sound288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node288 = Sparse.eval value288 (momentVector H) := by
  have heq : pivotMatrix288 = (fun u v => node288 (pivotPermutation288 u) v) := by apply Matrix.ext; unfold pivotMatrix288 node288 pivotPermutation288; decide +kernel
  have hmoment : injectiveMoment H node288 = injectiveMoment H pivotMatrix288 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix288 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix288 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix288 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (0 : Fin 3) = raw7457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw7457; decide +kernel
    rw [heq]
    exact (canonical7457 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix288 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (1 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix288 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix288 (2 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix288 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node288 + (injectiveMoment H (mergeFirst pivotMatrix288 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix288 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix288 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value288, value62, value63, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation289 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix289 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem sound289 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node289 = Sparse.eval value289 (momentVector H) := by
  have heq : pivotMatrix289 = (fun u v => node289 (pivotPermutation289 u) v) := by apply Matrix.ext; unfold pivotMatrix289 node289 pivotPermutation289; decide +kernel
  have hmoment : injectiveMoment H node289 = injectiveMoment H pivotMatrix289 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix289 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix289 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix289 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix289 (0 : Fin 3) = raw5550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix289 raw5550; decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix289 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix289 (1 : Fin 3) = raw7996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix289 raw7996; decide +kernel
    rw [heq]
    exact (canonical7996 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix289 (2 : Fin 3)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix289 (2 : Fin 3) = raw8006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix289 raw8006; decide +kernel
    rw [heq]
    exact (canonical8006 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node289 + (injectiveMoment H (mergeFirst pivotMatrix289 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix289 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix289 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value289, value3, value53, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation290 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix290 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

theorem sound290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node290 = Sparse.eval value290 (momentVector H) := by
  have heq : pivotMatrix290 = (fun u v => node290 (pivotPermutation290 u) v) := by apply Matrix.ext; unfold pivotMatrix290 node290 pivotPermutation290; decide +kernel
  have hmoment : injectiveMoment H node290 = injectiveMoment H pivotMatrix290 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix290 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix290 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix290 (0 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix290 (0 : Fin 3) = raw5552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix290 raw5552; decide +kernel
    rw [heq]
    exact (canonical5552 hH).trans (sound54 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix290 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix290 (1 : Fin 3) = raw7997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix290 raw7997; decide +kernel
    rw [heq]
    exact (canonical7997 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix290 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix290 (2 : Fin 3) = raw8007 := by apply Matrix.ext; unfold mergeFirst pivotMatrix290 raw8007; decide +kernel
    rw [heq]
    exact (canonical8007 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node290 + (injectiveMoment H (mergeFirst pivotMatrix290 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix290 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix290 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value290, value53, value54, value8, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation291 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix291 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem sound291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node291 = Sparse.eval value291 (momentVector H) := by
  have heq : pivotMatrix291 = (fun u v => node291 (pivotPermutation291 u) v) := by apply Matrix.ext; unfold pivotMatrix291 node291 pivotPermutation291; decide +kernel
  have hmoment : injectiveMoment H node291 = injectiveMoment H pivotMatrix291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix291 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix291 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (1 : Fin 3) = raw8167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8167; decide +kernel
    rw [heq]
    exact (canonical8167 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (2 : Fin 3) = raw8216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8216; decide +kernel
    rw [heq]
    exact (canonical8216 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node291 + (injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value291, value4, value57, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation292 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem sound292 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node292 = Sparse.eval value292 (momentVector H) := by
  have heq : pivotMatrix292 = (fun u v => node292 (pivotPermutation292 u) v) := by apply Matrix.ext; unfold pivotMatrix292 node292 pivotPermutation292; decide +kernel
  have hmoment : injectiveMoment H node292 = injectiveMoment H pivotMatrix292 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix292 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix292 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix292 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix292 (0 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix292 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix292 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix292 (1 : Fin 3) = raw8169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix292 raw8169; decide +kernel
    rw [heq]
    exact (canonical8169 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix292 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix292 (2 : Fin 3) = raw8217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix292 raw8217; decide +kernel
    rw [heq]
    exact (canonical8217 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node292 + (injectiveMoment H (mergeFirst pivotMatrix292 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix292 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix292 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value292, value10, value57, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation293 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix293 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem sound293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node293 = Sparse.eval value293 (momentVector H) := by
  have heq : pivotMatrix293 = (fun u v => node293 (pivotPermutation293 u) v) := by apply Matrix.ext; unfold pivotMatrix293 node293 pivotPermutation293; decide +kernel
  have hmoment : injectiveMoment H node293 = injectiveMoment H pivotMatrix293 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix293 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix293 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix293 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix293 (1 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (1 : Fin 3) = raw8542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw8542; decide +kernel
    rw [heq]
    exact (canonical8542 hH).trans (sound64 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix293 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (2 : Fin 3) = raw8697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw8697; decide +kernel
    rw [heq]
    exact (canonical8697 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node293 + (injectiveMoment H (mergeFirst pivotMatrix293 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix293 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix293 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value293, value5, value61, value64, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation294 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix294 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem sound294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node294 = Sparse.eval value294 (momentVector H) := by
  have heq : pivotMatrix294 = (fun u v => node294 (pivotPermutation294 u) v) := by apply Matrix.ext; unfold pivotMatrix294 node294 pivotPermutation294; decide +kernel
  have hmoment : injectiveMoment H node294 = injectiveMoment H pivotMatrix294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (1 : Fin 3) = raw8545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8545; decide +kernel
    rw [heq]
    exact (canonical8545 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (2 : Fin 3) = raw8778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8778; decide +kernel
    rw [heq]
    exact (canonical8778 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node294 + (injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value294, value11, value61, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation295 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix295 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem sound295 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node295 = Sparse.eval value295 (momentVector H) := by
  have heq : pivotMatrix295 = (fun u v => node295 (pivotPermutation295 u) v) := by apply Matrix.ext; unfold pivotMatrix295 node295 pivotPermutation295; decide +kernel
  have hmoment : injectiveMoment H node295 = injectiveMoment H pivotMatrix295 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix295 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix295 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix295 (0 : Fin 5)) =
      Sparse.eval value69 (momentVector H) := by
    have heq : mergeFirst pivotMatrix295 (0 : Fin 5) = raw207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix295 raw207; decide +kernel
    rw [heq]
    exact (canonical207 hH).trans (sound69 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix295 (1 : Fin 5)) =
      Sparse.eval value66 (momentVector H) := by
    have heq : mergeFirst pivotMatrix295 (1 : Fin 5) = raw49 := by apply Matrix.ext; unfold mergeFirst pivotMatrix295 raw49; decide +kernel
    rw [heq]
    exact (canonical49 hH).trans (sound66 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix295 (2 : Fin 5)) =
      Sparse.eval value66 (momentVector H) := by
    have heq : mergeFirst pivotMatrix295 (2 : Fin 5) = raw46 := by apply Matrix.ext; unfold mergeFirst pivotMatrix295 raw46; decide +kernel
    rw [heq]
    exact (canonical46 hH).trans (sound66 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix295 (3 : Fin 5)) =
      Sparse.eval value66 (momentVector H) := by
    have heq : mergeFirst pivotMatrix295 (3 : Fin 5) = raw44 := by apply Matrix.ext; unfold mergeFirst pivotMatrix295 raw44; decide +kernel
    rw [heq]
    exact (canonical44 hH).trans (sound66 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix295 (4 : Fin 5)) =
      Sparse.eval value66 (momentVector H) := by
    have heq : mergeFirst pivotMatrix295 (4 : Fin 5) = raw43 := by apply Matrix.ext; unfold mergeFirst pivotMatrix295 raw43; decide +kernel
    rw [heq]
    exact (canonical43 hH).trans (sound66 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node295 + (injectiveMoment H (mergeFirst pivotMatrix295 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix295 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix295 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix295 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix295 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value295, value66, value69, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation296 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix296 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem sound296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node296 = Sparse.eval value296 (momentVector H) := by
  have heq : pivotMatrix296 = (fun u v => node296 (pivotPermutation296 u) v) := by apply Matrix.ext; unfold pivotMatrix296 node296 pivotPermutation296; decide +kernel
  have hmoment : injectiveMoment H node296 = injectiveMoment H pivotMatrix296 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix296 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix296 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix296 (0 : Fin 5)) =
      Sparse.eval value66 (momentVector H) := by
    have heq : mergeFirst pivotMatrix296 (0 : Fin 5) = raw43 := by apply Matrix.ext; unfold mergeFirst pivotMatrix296 raw43; decide +kernel
    rw [heq]
    exact (canonical43 hH).trans (sound66 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix296 (1 : Fin 5)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix296 (1 : Fin 5) = raw197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix296 raw197; decide +kernel
    rw [heq]
    exact (canonical197 hH).trans (sound16 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix296 (2 : Fin 5)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix296 (2 : Fin 5) = raw201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix296 raw201; decide +kernel
    rw [heq]
    exact (canonical201 hH).trans (sound16 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix296 (3 : Fin 5)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix296 (3 : Fin 5) = raw206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix296 raw206; decide +kernel
    rw [heq]
    exact (canonical206 hH).trans (sound16 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix296 (4 : Fin 5)) =
      Sparse.eval value69 (momentVector H) := by
    have heq : mergeFirst pivotMatrix296 (4 : Fin 5) = raw207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix296 raw207; decide +kernel
    rw [heq]
    exact (canonical207 hH).trans (sound69 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node296 + (injectiveMoment H (mergeFirst pivotMatrix296 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix296 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix296 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix296 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix296 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value296, value16, value66, value69, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation297 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix297 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem sound297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node297 = Sparse.eval value297 (momentVector H) := by
  have heq : pivotMatrix297 = (fun u v => node297 (pivotPermutation297 u) v) := by apply Matrix.ext; unfold pivotMatrix297 node297 pivotPermutation297; decide +kernel
  have hmoment : injectiveMoment H node297 = injectiveMoment H pivotMatrix297 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix297 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix297 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix297 (0 : Fin 4)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix297 (0 : Fin 4) = raw295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix297 raw295; decide +kernel
    rw [heq]
    exact (canonical295 hH).trans (sound243 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix297 (1 : Fin 4)) =
      Sparse.eval value73 (momentVector H) := by
    have heq : mergeFirst pivotMatrix297 (1 : Fin 4) = raw236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix297 raw236; decide +kernel
    rw [heq]
    exact (canonical236 hH).trans (sound73 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix297 (2 : Fin 4)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix297 (2 : Fin 4) = raw229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix297 raw229; decide +kernel
    rw [heq]
    exact (canonical229 hH).trans (sound123 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix297 (3 : Fin 4)) =
      Sparse.eval value71 (momentVector H) := by
    have heq : mergeFirst pivotMatrix297 (3 : Fin 4) = raw227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix297 raw227; decide +kernel
    rw [heq]
    exact (canonical227 hH).trans (sound71 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node297 + (injectiveMoment H (mergeFirst pivotMatrix297 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix297 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix297 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix297 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value297, value123, value243, value71, value73, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation298 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix298 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem sound298 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node298 = Sparse.eval value298 (momentVector H) := by
  have heq : pivotMatrix298 = (fun u v => node298 (pivotPermutation298 u) v) := by apply Matrix.ext; unfold pivotMatrix298 node298 pivotPermutation298; decide +kernel
  have hmoment : injectiveMoment H node298 = injectiveMoment H pivotMatrix298 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix298 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix298 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix298 (0 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix298 (0 : Fin 4) = raw297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix298 raw297; decide +kernel
    rw [heq]
    exact (canonical297 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix298 (1 : Fin 4)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix298 (1 : Fin 4) = raw239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix298 raw239; decide +kernel
    rw [heq]
    exact (canonical239 hH).trans (sound74 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix298 (2 : Fin 4)) =
      Sparse.eval value72 (momentVector H) := by
    have heq : mergeFirst pivotMatrix298 (2 : Fin 4) = raw231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix298 raw231; decide +kernel
    rw [heq]
    exact (canonical231 hH).trans (sound72 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix298 (3 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix298 (3 : Fin 4) = raw230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix298 raw230; decide +kernel
    rw [heq]
    exact (canonical230 hH).trans (sound127 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node298 + (injectiveMoment H (mergeFirst pivotMatrix298 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix298 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix298 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix298 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value298, value127, value246, value72, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation299 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix299 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem sound299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node299 = Sparse.eval value299 (momentVector H) := by
  have heq : pivotMatrix299 = (fun u v => node299 (pivotPermutation299 u) v) := by apply Matrix.ext; unfold pivotMatrix299 node299 pivotPermutation299; decide +kernel
  have hmoment : injectiveMoment H node299 = injectiveMoment H pivotMatrix299 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix299 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix299 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix299 (0 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix299 (0 : Fin 4) = raw307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix299 raw307; decide +kernel
    rw [heq]
    exact (canonical307 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix299 (1 : Fin 4)) =
      Sparse.eval value75 (momentVector H) := by
    have heq : mergeFirst pivotMatrix299 (1 : Fin 4) = raw243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix299 raw243; decide +kernel
    rw [heq]
    exact (canonical243 hH).trans (sound75 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix299 (2 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix299 (2 : Fin 4) = raw238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix299 raw238; decide +kernel
    rw [heq]
    exact (canonical238 hH).trans (sound120 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix299 (3 : Fin 4)) =
      Sparse.eval value73 (momentVector H) := by
    have heq : mergeFirst pivotMatrix299 (3 : Fin 4) = raw236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix299 raw236; decide +kernel
    rw [heq]
    exact (canonical236 hH).trans (sound73 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node299 + (injectiveMoment H (mergeFirst pivotMatrix299 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix299 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix299 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix299 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value299, value120, value201, value73, value75, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation300 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix300 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem sound300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node300 = Sparse.eval value300 (momentVector H) := by
  have heq : pivotMatrix300 = (fun u v => node300 (pivotPermutation300 u) v) := by apply Matrix.ext; unfold pivotMatrix300 node300 pivotPermutation300; decide +kernel
  have hmoment : injectiveMoment H node300 = injectiveMoment H pivotMatrix300 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix300 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix300 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix300 (0 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix300 (0 : Fin 4) = raw309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix300 raw309; decide +kernel
    rw [heq]
    exact (canonical309 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix300 (1 : Fin 4)) =
      Sparse.eval value76 (momentVector H) := by
    have heq : mergeFirst pivotMatrix300 (1 : Fin 4) = raw244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix300 raw244; decide +kernel
    rw [heq]
    exact (canonical244 hH).trans (sound76 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix300 (2 : Fin 4)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix300 (2 : Fin 4) = raw239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix300 raw239; decide +kernel
    rw [heq]
    exact (canonical239 hH).trans (sound74 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix300 (3 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix300 (3 : Fin 4) = raw238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix300 raw238; decide +kernel
    rw [heq]
    exact (canonical238 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node300 + (injectiveMoment H (mergeFirst pivotMatrix300 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix300 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix300 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix300 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value300, value120, value206, value74, value76, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation301 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix301 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem sound301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node301 = Sparse.eval value301 (momentVector H) := by
  have heq : pivotMatrix301 = (fun u v => node301 (pivotPermutation301 u) v) := by apply Matrix.ext; unfold pivotMatrix301 node301 pivotPermutation301; decide +kernel
  have hmoment : injectiveMoment H node301 = injectiveMoment H pivotMatrix301 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix301 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix301 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix301 (0 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix301 (0 : Fin 4) = raw326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix301 raw326; decide +kernel
    rw [heq]
    exact (canonical326 hH).trans (sound173 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix301 (1 : Fin 4)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix301 (1 : Fin 4) = raw251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix301 raw251; decide +kernel
    rw [heq]
    exact (canonical251 hH).trans (sound119 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix301 (2 : Fin 4)) =
      Sparse.eval value78 (momentVector H) := by
    have heq : mergeFirst pivotMatrix301 (2 : Fin 4) = raw248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix301 raw248; decide +kernel
    rw [heq]
    exact (canonical248 hH).trans (sound78 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix301 (3 : Fin 4)) =
      Sparse.eval value77 (momentVector H) := by
    have heq : mergeFirst pivotMatrix301 (3 : Fin 4) = raw247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix301 raw247; decide +kernel
    rw [heq]
    exact (canonical247 hH).trans (sound77 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node301 + (injectiveMoment H (mergeFirst pivotMatrix301 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix301 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix301 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix301 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value301, value119, value173, value77, value78, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation302 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix302 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem sound302 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node302 = Sparse.eval value302 (momentVector H) := by
  have heq : pivotMatrix302 = (fun u v => node302 (pivotPermutation302 u) v) := by apply Matrix.ext; unfold pivotMatrix302 node302 pivotPermutation302; decide +kernel
  have hmoment : injectiveMoment H node302 = injectiveMoment H pivotMatrix302 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix302 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix302 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix302 (0 : Fin 4)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix302 (0 : Fin 4) = raw327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix302 raw327; decide +kernel
    rw [heq]
    exact (canonical327 hH).trans (sound244 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix302 (1 : Fin 4)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix302 (1 : Fin 4) = raw252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix302 raw252; decide +kernel
    rw [heq]
    exact (canonical252 hH).trans (sound124 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix302 (2 : Fin 4)) =
      Sparse.eval value78 (momentVector H) := by
    have heq : mergeFirst pivotMatrix302 (2 : Fin 4) = raw249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix302 raw249; decide +kernel
    rw [heq]
    exact (canonical249 hH).trans (sound78 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix302 (3 : Fin 4)) =
      Sparse.eval value78 (momentVector H) := by
    have heq : mergeFirst pivotMatrix302 (3 : Fin 4) = raw248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix302 raw248; decide +kernel
    rw [heq]
    exact (canonical248 hH).trans (sound78 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node302 + (injectiveMoment H (mergeFirst pivotMatrix302 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix302 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix302 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix302 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value302, value124, value244, value78, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation303 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix303 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node303 = Sparse.eval value303 (momentVector H) := by
  have heq : pivotMatrix303 = (fun u v => node303 (pivotPermutation303 u) v) := by apply Matrix.ext; unfold pivotMatrix303 node303 pivotPermutation303; decide +kernel
  have hmoment : injectiveMoment H node303 = injectiveMoment H pivotMatrix303 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix303 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix303 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix303 (0 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix303 (0 : Fin 4) = raw953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix303 raw953; decide +kernel
    rw [heq]
    exact (canonical953 hH).trans (sound127 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix303 (1 : Fin 4)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix303 (1 : Fin 4) = raw254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix303 raw254; decide +kernel
    rw [heq]
    exact (canonical254 hH).trans (sound124 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix303 (2 : Fin 4)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix303 (2 : Fin 4) = raw240 := by apply Matrix.ext; unfold mergeFirst pivotMatrix303 raw240; decide +kernel
    rw [heq]
    exact (canonical240 hH).trans (sound74 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix303 (3 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix303 (3 : Fin 4) = raw238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix303 raw238; decide +kernel
    rw [heq]
    exact (canonical238 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node303 + (injectiveMoment H (mergeFirst pivotMatrix303 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix303 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix303 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix303 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value303, value120, value124, value127, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation304 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix304 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound304 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node304 = Sparse.eval value304 (momentVector H) := by
  have heq : pivotMatrix304 = (fun u v => node304 (pivotPermutation304 u) v) := by apply Matrix.ext; unfold pivotMatrix304 node304 pivotPermutation304; decide +kernel
  have hmoment : injectiveMoment H node304 = injectiveMoment H pivotMatrix304 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix304 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix304 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix304 (0 : Fin 4)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix304 (0 : Fin 4) = raw957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix304 raw957; decide +kernel
    rw [heq]
    exact (canonical957 hH).trans (sound129 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix304 (1 : Fin 4)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix304 (1 : Fin 4) = raw256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix304 raw256; decide +kernel
    rw [heq]
    exact (canonical256 hH).trans (sound119 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix304 (2 : Fin 4)) =
      Sparse.eval value76 (momentVector H) := by
    have heq : mergeFirst pivotMatrix304 (2 : Fin 4) = raw245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix304 raw245; decide +kernel
    rw [heq]
    exact (canonical245 hH).trans (sound76 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix304 (3 : Fin 4)) =
      Sparse.eval value76 (momentVector H) := by
    have heq : mergeFirst pivotMatrix304 (3 : Fin 4) = raw244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix304 raw244; decide +kernel
    rw [heq]
    exact (canonical244 hH).trans (sound76 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node304 + (injectiveMoment H (mergeFirst pivotMatrix304 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix304 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix304 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix304 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value304, value119, value129, value76, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation305 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix305 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem sound305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node305 = Sparse.eval value305 (momentVector H) := by
  have heq : pivotMatrix305 = (fun u v => node305 (pivotPermutation305 u) v) := by apply Matrix.ext; unfold pivotMatrix305 node305 pivotPermutation305; decide +kernel
  have hmoment : injectiveMoment H node305 = injectiveMoment H pivotMatrix305 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix305 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix305 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix305 (0 : Fin 4)) =
      Sparse.eval value70 (momentVector H) := by
    have heq : mergeFirst pivotMatrix305 (0 : Fin 4) = raw224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix305 raw224; decide +kernel
    rw [heq]
    exact (canonical224 hH).trans (sound70 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix305 (1 : Fin 4)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix305 (1 : Fin 4) = raw276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix305 raw276; decide +kernel
    rw [heq]
    exact (canonical276 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix305 (2 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix305 (2 : Fin 4) = raw285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix305 raw285; decide +kernel
    rw [heq]
    exact (canonical285 hH).trans (sound248 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix305 (3 : Fin 4)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix305 (3 : Fin 4) = raw289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix305 raw289; decide +kernel
    rw [heq]
    exact (canonical289 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node305 + (injectiveMoment H (mergeFirst pivotMatrix305 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix305 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix305 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix305 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value305, value248, value32, value70, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation306 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix306 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem sound306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node306 = Sparse.eval value306 (momentVector H) := by
  have heq : pivotMatrix306 = (fun u v => node306 (pivotPermutation306 u) v) := by apply Matrix.ext; unfold pivotMatrix306 node306 pivotPermutation306; decide +kernel
  have hmoment : injectiveMoment H node306 = injectiveMoment H pivotMatrix306 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix306 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix306 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix306 (0 : Fin 4)) =
      Sparse.eval value71 (momentVector H) := by
    have heq : mergeFirst pivotMatrix306 (0 : Fin 4) = raw227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix306 raw227; decide +kernel
    rw [heq]
    exact (canonical227 hH).trans (sound71 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix306 (1 : Fin 4)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix306 (1 : Fin 4) = raw278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix306 raw278; decide +kernel
    rw [heq]
    exact (canonical278 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix306 (2 : Fin 4)) =
      Sparse.eval value82 (momentVector H) := by
    have heq : mergeFirst pivotMatrix306 (2 : Fin 4) = raw292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix306 raw292; decide +kernel
    rw [heq]
    exact (canonical292 hH).trans (sound82 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix306 (3 : Fin 4)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix306 (3 : Fin 4) = raw295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix306 raw295; decide +kernel
    rw [heq]
    exact (canonical295 hH).trans (sound243 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node306 + (injectiveMoment H (mergeFirst pivotMatrix306 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix306 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix306 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix306 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value306, value243, value59, value71, value82, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation307 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix307 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem sound307 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node307 = Sparse.eval value307 (momentVector H) := by
  have heq : pivotMatrix307 = (fun u v => node307 (pivotPermutation307 u) v) := by apply Matrix.ext; unfold pivotMatrix307 node307 pivotPermutation307; decide +kernel
  have hmoment : injectiveMoment H node307 = injectiveMoment H pivotMatrix307 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix307 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix307 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix307 (0 : Fin 4)) =
      Sparse.eval value72 (momentVector H) := by
    have heq : mergeFirst pivotMatrix307 (0 : Fin 4) = raw231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix307 raw231; decide +kernel
    rw [heq]
    exact (canonical231 hH).trans (sound72 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix307 (1 : Fin 4)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix307 (1 : Fin 4) = raw279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix307 raw279; decide +kernel
    rw [heq]
    exact (canonical279 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix307 (2 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix307 (2 : Fin 4) = raw297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix307 raw297; decide +kernel
    rw [heq]
    exact (canonical297 hH).trans (sound246 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix307 (3 : Fin 4)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix307 (3 : Fin 4) = raw298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix307 raw298; decide +kernel
    rw [heq]
    exact (canonical298 hH).trans (sound83 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node307 + (injectiveMoment H (mergeFirst pivotMatrix307 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix307 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix307 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix307 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value307, value246, value40, value72, value83, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation308 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix308 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem sound308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node308 = Sparse.eval value308 (momentVector H) := by
  have heq : pivotMatrix308 = (fun u v => node308 (pivotPermutation308 u) v) := by apply Matrix.ext; unfold pivotMatrix308 node308 pivotPermutation308; decide +kernel
  have hmoment : injectiveMoment H node308 = injectiveMoment H pivotMatrix308 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix308 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix308 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix308 (0 : Fin 4)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix308 (0 : Fin 4) = raw239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix308 raw239; decide +kernel
    rw [heq]
    exact (canonical239 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix308 (1 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix308 (1 : Fin 4) = raw297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix308 raw297; decide +kernel
    rw [heq]
    exact (canonical297 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix308 (2 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix308 (2 : Fin 4) = raw309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix308 raw309; decide +kernel
    rw [heq]
    exact (canonical309 hH).trans (sound206 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix308 (3 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix308 (3 : Fin 4) = raw310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix308 raw310; decide +kernel
    rw [heq]
    exact (canonical310 hH).trans (sound85 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node308 + (injectiveMoment H (mergeFirst pivotMatrix308 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix308 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix308 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix308 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value308, value206, value246, value74, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation309 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix309 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem sound309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node309 = Sparse.eval value309 (momentVector H) := by
  have heq : pivotMatrix309 = (fun u v => node309 (pivotPermutation309 u) v) := by apply Matrix.ext; unfold pivotMatrix309 node309 pivotPermutation309; decide +kernel
  have hmoment : injectiveMoment H node309 = injectiveMoment H pivotMatrix309 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix309 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix309 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix309 (0 : Fin 4)) =
      Sparse.eval value75 (momentVector H) := by
    have heq : mergeFirst pivotMatrix309 (0 : Fin 4) = raw243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix309 raw243; decide +kernel
    rw [heq]
    exact (canonical243 hH).trans (sound75 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix309 (1 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix309 (1 : Fin 4) = raw307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix309 raw307; decide +kernel
    rw [heq]
    exact (canonical307 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix309 (2 : Fin 4)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix309 (2 : Fin 4) = raw314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix309 raw314; decide +kernel
    rw [heq]
    exact (canonical314 hH).trans (sound86 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix309 (3 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix309 (3 : Fin 4) = raw317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix309 raw317; decide +kernel
    rw [heq]
    exact (canonical317 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node309 + (injectiveMoment H (mergeFirst pivotMatrix309 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix309 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix309 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix309 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value309, value201, value75, value86, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation310 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix310 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem sound310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node310 = Sparse.eval value310 (momentVector H) := by
  have heq : pivotMatrix310 = (fun u v => node310 (pivotPermutation310 u) v) := by apply Matrix.ext; unfold pivotMatrix310 node310 pivotPermutation310; decide +kernel
  have hmoment : injectiveMoment H node310 = injectiveMoment H pivotMatrix310 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix310 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix310 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix310 (0 : Fin 4)) =
      Sparse.eval value76 (momentVector H) := by
    have heq : mergeFirst pivotMatrix310 (0 : Fin 4) = raw244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix310 raw244; decide +kernel
    rw [heq]
    exact (canonical244 hH).trans (sound76 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix310 (1 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix310 (1 : Fin 4) = raw309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix310 raw309; decide +kernel
    rw [heq]
    exact (canonical309 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix310 (2 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix310 (2 : Fin 4) = raw317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix310 raw317; decide +kernel
    rw [heq]
    exact (canonical317 hH).trans (sound87 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix310 (3 : Fin 4)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix310 (3 : Fin 4) = raw318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix310 raw318; decide +kernel
    rw [heq]
    exact (canonical318 hH).trans (sound88 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node310 + (injectiveMoment H (mergeFirst pivotMatrix310 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix310 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix310 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix310 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value310, value206, value76, value87, value88, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation311 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix311 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

theorem sound311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node311 = Sparse.eval value311 (momentVector H) := by
  have heq : pivotMatrix311 = (fun u v => node311 (pivotPermutation311 u) v) := by apply Matrix.ext; unfold pivotMatrix311 node311 pivotPermutation311; decide +kernel
  have hmoment : injectiveMoment H node311 = injectiveMoment H pivotMatrix311 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix311 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix311 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix311 (0 : Fin 4)) =
      Sparse.eval value77 (momentVector H) := by
    have heq : mergeFirst pivotMatrix311 (0 : Fin 4) = raw247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix311 raw247; decide +kernel
    rw [heq]
    exact (canonical247 hH).trans (sound77 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix311 (1 : Fin 4)) =
      Sparse.eval value80 (momentVector H) := by
    have heq : mergeFirst pivotMatrix311 (1 : Fin 4) = raw321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix311 raw321; decide +kernel
    rw [heq]
    exact (canonical321 hH).trans (sound80 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix311 (2 : Fin 4)) =
      Sparse.eval value90 (momentVector H) := by
    have heq : mergeFirst pivotMatrix311 (2 : Fin 4) = raw325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix311 raw325; decide +kernel
    rw [heq]
    exact (canonical325 hH).trans (sound90 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix311 (3 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix311 (3 : Fin 4) = raw326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix311 raw326; decide +kernel
    rw [heq]
    exact (canonical326 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node311 + (injectiveMoment H (mergeFirst pivotMatrix311 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix311 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix311 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix311 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value311, value173, value77, value80, value90, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation312 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix312 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

theorem sound312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node312 = Sparse.eval value312 (momentVector H) := by
  have heq : pivotMatrix312 = (fun u v => node312 (pivotPermutation312 u) v) := by apply Matrix.ext; unfold pivotMatrix312 node312 pivotPermutation312; decide +kernel
  have hmoment : injectiveMoment H node312 = injectiveMoment H pivotMatrix312 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix312 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix312 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix312 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix312 (0 : Fin 4) = raw522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix312 raw522; decide +kernel
    rw [heq]
    exact (canonical522 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix312 (1 : Fin 4)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix312 (1 : Fin 4) = raw302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix312 raw302; decide +kernel
    rw [heq]
    exact (canonical302 hH).trans (sound81 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix312 (2 : Fin 4)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix312 (2 : Fin 4) = raw289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix312 raw289; decide +kernel
    rw [heq]
    exact (canonical289 hH).trans (sound81 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix312 (3 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix312 (3 : Fin 4) = raw285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix312 raw285; decide +kernel
    rw [heq]
    exact (canonical285 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node312 + (injectiveMoment H (mergeFirst pivotMatrix312 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix312 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix312 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix312 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value312, value188, value248, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation313 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix313 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem sound313 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node313 = Sparse.eval value313 (momentVector H) := by
  have heq : pivotMatrix313 = (fun u v => node313 (pivotPermutation313 u) v) := by apply Matrix.ext; unfold pivotMatrix313 node313 pivotPermutation313; decide +kernel
  have hmoment : injectiveMoment H node313 = injectiveMoment H pivotMatrix313 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix313 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix313 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix313 (0 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix313 (0 : Fin 4) = raw532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix313 raw532; decide +kernel
    rw [heq]
    exact (canonical532 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix313 (1 : Fin 4)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix313 (1 : Fin 4) = raw304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix313 raw304; decide +kernel
    rw [heq]
    exact (canonical304 hH).trans (sound84 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix313 (2 : Fin 4)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix313 (2 : Fin 4) = raw295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix313 raw295; decide +kernel
    rw [heq]
    exact (canonical295 hH).trans (sound243 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix313 (3 : Fin 4)) =
      Sparse.eval value82 (momentVector H) := by
    have heq : mergeFirst pivotMatrix313 (3 : Fin 4) = raw292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix313 raw292; decide +kernel
    rw [heq]
    exact (canonical292 hH).trans (sound82 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node313 + (injectiveMoment H (mergeFirst pivotMatrix313 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix313 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix313 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix313 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value313, value222, value243, value82, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation314 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix314 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem sound314 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node314 = Sparse.eval value314 (momentVector H) := by
  have heq : pivotMatrix314 = (fun u v => node314 (pivotPermutation314 u) v) := by apply Matrix.ext; unfold pivotMatrix314 node314 pivotPermutation314; decide +kernel
  have hmoment : injectiveMoment H node314 = injectiveMoment H pivotMatrix314 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix314 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix314 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix314 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix314 (0 : Fin 4) = raw538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix314 raw538; decide +kernel
    rw [heq]
    exact (canonical538 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix314 (1 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix314 (1 : Fin 4) = raw310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix314 raw310; decide +kernel
    rw [heq]
    exact (canonical310 hH).trans (sound85 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix314 (2 : Fin 4)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix314 (2 : Fin 4) = raw298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix314 raw298; decide +kernel
    rw [heq]
    exact (canonical298 hH).trans (sound83 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix314 (3 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix314 (3 : Fin 4) = raw297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix314 raw297; decide +kernel
    rw [heq]
    exact (canonical297 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node314 + (injectiveMoment H (mergeFirst pivotMatrix314 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix314 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix314 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix314 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value314, value215, value246, value83, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation315 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix315 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem sound315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node315 = Sparse.eval value315 (momentVector H) := by
  have heq : pivotMatrix315 = (fun u v => node315 (pivotPermutation315 u) v) := by apply Matrix.ext; unfold pivotMatrix315 node315 pivotPermutation315; decide +kernel
  have hmoment : injectiveMoment H node315 = injectiveMoment H pivotMatrix315 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix315 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix315 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix315 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix315 (0 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix315 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix315 (1 : Fin 4)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix315 (1 : Fin 4) = raw314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix315 raw314; decide +kernel
    rw [heq]
    exact (canonical314 hH).trans (sound86 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix315 (2 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix315 (2 : Fin 4) = raw307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix315 raw307; decide +kernel
    rw [heq]
    exact (canonical307 hH).trans (sound201 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix315 (3 : Fin 4)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix315 (3 : Fin 4) = raw304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix315 raw304; decide +kernel
    rw [heq]
    exact (canonical304 hH).trans (sound84 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node315 + (injectiveMoment H (mergeFirst pivotMatrix315 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix315 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix315 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix315 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value315, value198, value201, value84, value86, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation316 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix316 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem sound316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node316 = Sparse.eval value316 (momentVector H) := by
  have heq : pivotMatrix316 = (fun u v => node316 (pivotPermutation316 u) v) := by apply Matrix.ext; unfold pivotMatrix316 node316 pivotPermutation316; decide +kernel
  have hmoment : injectiveMoment H node316 = injectiveMoment H pivotMatrix316 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix316 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix316 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix316 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix316 (0 : Fin 4) = raw552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix316 raw552; decide +kernel
    rw [heq]
    exact (canonical552 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix316 (1 : Fin 4)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix316 (1 : Fin 4) = raw317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix316 raw317; decide +kernel
    rw [heq]
    exact (canonical317 hH).trans (sound87 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix316 (2 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix316 (2 : Fin 4) = raw309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix316 raw309; decide +kernel
    rw [heq]
    exact (canonical309 hH).trans (sound206 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix316 (3 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix316 (3 : Fin 4) = raw307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix316 raw307; decide +kernel
    rw [heq]
    exact (canonical307 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node316 + (injectiveMoment H (mergeFirst pivotMatrix316 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix316 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix316 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix316 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value316, value201, value206, value215, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation317 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix317 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem sound317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node317 = Sparse.eval value317 (momentVector H) := by
  have heq : pivotMatrix317 = (fun u v => node317 (pivotPermutation317 u) v) := by apply Matrix.ext; unfold pivotMatrix317 node317 pivotPermutation317; decide +kernel
  have hmoment : injectiveMoment H node317 = injectiveMoment H pivotMatrix317 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix317 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix317 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix317 (0 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix317 (0 : Fin 4) = raw553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix317 raw553; decide +kernel
    rw [heq]
    exact (canonical553 hH).trans (sound204 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix317 (1 : Fin 4)) =
      Sparse.eval value88 (momentVector H) := by
    have heq : mergeFirst pivotMatrix317 (1 : Fin 4) = raw318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix317 raw318; decide +kernel
    rw [heq]
    exact (canonical318 hH).trans (sound88 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix317 (2 : Fin 4)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix317 (2 : Fin 4) = raw310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix317 raw310; decide +kernel
    rw [heq]
    exact (canonical310 hH).trans (sound85 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix317 (3 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix317 (3 : Fin 4) = raw309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix317 raw309; decide +kernel
    rw [heq]
    exact (canonical309 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node317 + (injectiveMoment H (mergeFirst pivotMatrix317 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix317 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix317 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix317 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value317, value204, value206, value85, value88, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation318 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix318 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem sound318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node318 = Sparse.eval value318 (momentVector H) := by
  have heq : pivotMatrix318 = (fun u v => node318 (pivotPermutation318 u) v) := by apply Matrix.ext; unfold pivotMatrix318 node318 pivotPermutation318; decide +kernel
  have hmoment : injectiveMoment H node318 = injectiveMoment H pivotMatrix318 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix318 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix318 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix318 (0 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix318 (0 : Fin 4) = raw575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix318 raw575; decide +kernel
    rw [heq]
    exact (canonical575 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix318 (1 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix318 (1 : Fin 4) = raw326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix318 raw326; decide +kernel
    rw [heq]
    exact (canonical326 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix318 (2 : Fin 4)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix318 (2 : Fin 4) = raw322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix318 raw322; decide +kernel
    rw [heq]
    exact (canonical322 hH).trans (sound89 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix318 (3 : Fin 4)) =
      Sparse.eval value80 (momentVector H) := by
    have heq : mergeFirst pivotMatrix318 (3 : Fin 4) = raw321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix318 raw321; decide +kernel
    rw [heq]
    exact (canonical321 hH).trans (sound80 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node318 + (injectiveMoment H (mergeFirst pivotMatrix318 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix318 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix318 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix318 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value318, value170, value173, value80, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation319 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix319 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

theorem sound319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node319 = Sparse.eval value319 (momentVector H) := by
  have heq : pivotMatrix319 = (fun u v => node319 (pivotPermutation319 u) v) := by apply Matrix.ext; unfold pivotMatrix319 node319 pivotPermutation319; decide +kernel
  have hmoment : injectiveMoment H node319 = injectiveMoment H pivotMatrix319 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix319 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix319 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix319 (0 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix319 (0 : Fin 4) = raw576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix319 raw576; decide +kernel
    rw [heq]
    exact (canonical576 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix319 (1 : Fin 4)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix319 (1 : Fin 4) = raw327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix319 raw327; decide +kernel
    rw [heq]
    exact (canonical327 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix319 (2 : Fin 4)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix319 (2 : Fin 4) = raw323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix319 raw323; decide +kernel
    rw [heq]
    exact (canonical323 hH).trans (sound89 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix319 (3 : Fin 4)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix319 (3 : Fin 4) = raw322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix319 raw322; decide +kernel
    rw [heq]
    exact (canonical322 hH).trans (sound89 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node319 + (injectiveMoment H (mergeFirst pivotMatrix319 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix319 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix319 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix319 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value319, value223, value244, value89, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
