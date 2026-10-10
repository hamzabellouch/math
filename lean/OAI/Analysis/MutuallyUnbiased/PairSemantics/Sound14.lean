import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation896 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix896 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

theorem sound896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node896 = Sparse.eval value896 (momentVector H) := by
  have heq : pivotMatrix896 = (fun u v => node896.transpose (pivotPermutation896 u) v) := by apply Matrix.ext; unfold pivotMatrix896 node896 pivotPermutation896; decide +kernel
  have hmoment : injectiveMoment H node896 = injectiveMoment H pivotMatrix896 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix896 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix896 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix896 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (0 : Fin 3) = raw2524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw2524; decide +kernel
    rw [heq]
    exact (canonical2524 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix896 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (1 : Fin 3) = raw6889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw6889; decide +kernel
    rw [heq]
    exact (canonical6889 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix896 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (2 : Fin 3) = raw6895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw6895; decide +kernel
    rw [heq]
    exact (canonical6895 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node896 + (injectiveMoment H (mergeFirst pivotMatrix896 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix896 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix896 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value896, value134, value225, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation897 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix897 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3]]

theorem sound897 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node897 = Sparse.eval value897 (momentVector H) := by
  have heq : pivotMatrix897 = (fun u v => node897 (pivotPermutation897 u) v) := by apply Matrix.ext; unfold pivotMatrix897 node897 pivotPermutation897; decide +kernel
  have hmoment : injectiveMoment H node897 = injectiveMoment H pivotMatrix897 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix897 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix897 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix897 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix897 (0 : Fin 3) = raw8278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix897 raw8278; decide +kernel
    rw [heq]
    exact (canonical8278 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix897 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix897 (1 : Fin 3) = raw6115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix897 raw6115; decide +kernel
    rw [heq]
    exact (canonical6115 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix897 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix897 (2 : Fin 3) = raw6046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix897 raw6046; decide +kernel
    rw [heq]
    exact (canonical6046 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node897 + (injectiveMoment H (mergeFirst pivotMatrix897 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix897 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix897 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value897, value206, value246, value40, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation898 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix898 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![1, 1, 0, -2]]

theorem sound898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node898 = Sparse.eval value898 (momentVector H) := by
  have heq : pivotMatrix898 = (fun u v => node898 (pivotPermutation898 u) v) := by apply Matrix.ext; unfold pivotMatrix898 node898 pivotPermutation898; decide +kernel
  have hmoment : injectiveMoment H node898 = injectiveMoment H pivotMatrix898 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix898 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix898 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix898 (0 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix898 (0 : Fin 3) = raw7004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix898 raw7004; decide +kernel
    rw [heq]
    exact (canonical7004 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix898 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix898 (1 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix898 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix898 (2 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix898 (2 : Fin 3) = raw6051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix898 raw6051; decide +kernel
    rw [heq]
    exact (canonical6051 hH).trans (sound106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node898 + (injectiveMoment H (mergeFirst pivotMatrix898 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix898 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix898 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value898, value106, value145, value155, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation899 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix899 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![1, 1, -1, -1]]

theorem sound899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node899 = Sparse.eval value899 (momentVector H) := by
  have heq : pivotMatrix899 = (fun u v => node899 (pivotPermutation899 u) v) := by apply Matrix.ext; unfold pivotMatrix899 node899 pivotPermutation899; decide +kernel
  have hmoment : injectiveMoment H node899 = injectiveMoment H pivotMatrix899 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix899 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix899 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix899 (0 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix899 (0 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix899 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix899 (1 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix899 (1 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix899 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix899 (2 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix899 (2 : Fin 3) = raw6051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix899 raw6051; decide +kernel
    rw [heq]
    exact (canonical6051 hH).trans (sound106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node899 + (injectiveMoment H (mergeFirst pivotMatrix899 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix899 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix899 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value899, value106, value248, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation900 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix900 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-2, 3, 1, -2], ![4, -2, -2, 0]]

theorem sound900 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node900 = Sparse.eval value900 (momentVector H) := by
  have heq : pivotMatrix900 = (fun u v => node900.transpose (pivotPermutation900 u) v) := by apply Matrix.ext; unfold pivotMatrix900 node900 pivotPermutation900; decide +kernel
  have hmoment : injectiveMoment H node900 = injectiveMoment H pivotMatrix900 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix900 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix900 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix900 (0 : Fin 3)) =
      Sparse.eval value136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix900 (0 : Fin 3) = raw2135 := by apply Matrix.ext; unfold mergeFirst pivotMatrix900 raw2135; decide +kernel
    rw [heq]
    exact (canonical2135 hH).trans (sound136 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix900 (1 : Fin 3)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix900 (1 : Fin 3) = raw6571 := by apply Matrix.ext; unfold mergeFirst pivotMatrix900 raw6571; decide +kernel
    rw [heq]
    exact (canonical6571 hH).trans (sound247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix900 (2 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix900 (2 : Fin 3) = raw6577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix900 raw6577; decide +kernel
    rw [heq]
    exact (canonical6577 hH).trans (sound262 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node900 + (injectiveMoment H (mergeFirst pivotMatrix900 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix900 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix900 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value900, value136, value247, value262, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation901 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix901 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-2, 3, -2, 1], ![4, -2, 0, -2]]

theorem sound901 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node901 = Sparse.eval value901 (momentVector H) := by
  have heq : pivotMatrix901 = (fun u v => node901.transpose (pivotPermutation901 u) v) := by apply Matrix.ext; unfold pivotMatrix901 node901 pivotPermutation901; decide +kernel
  have hmoment : injectiveMoment H node901 = injectiveMoment H pivotMatrix901 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix901 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix901 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix901 (0 : Fin 3)) =
      Sparse.eval value136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix901 (0 : Fin 3) = raw2526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix901 raw2526; decide +kernel
    rw [heq]
    exact (canonical2526 hH).trans (sound136 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix901 (1 : Fin 3)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix901 (1 : Fin 3) = raw6891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix901 raw6891; decide +kernel
    rw [heq]
    exact (canonical6891 hH).trans (sound211 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix901 (2 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix901 (2 : Fin 3) = raw6897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix901 raw6897; decide +kernel
    rw [heq]
    exact (canonical6897 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node901 + (injectiveMoment H (mergeFirst pivotMatrix901 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix901 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix901 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value901, value136, value209, value211, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation902 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix902 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1]]

theorem sound902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node902 = Sparse.eval value902 (momentVector H) := by
  have heq : pivotMatrix902 = (fun u v => node902 (pivotPermutation902 u) v) := by apply Matrix.ext; unfold pivotMatrix902 node902 pivotPermutation902; decide +kernel
  have hmoment : injectiveMoment H node902 = injectiveMoment H pivotMatrix902 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix902 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix902 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix902 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix902 (0 : Fin 3) = raw8296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix902 raw8296; decide +kernel
    rw [heq]
    exact (canonical8296 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix902 (1 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix902 (1 : Fin 3) = raw6117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix902 raw6117; decide +kernel
    rw [heq]
    exact (canonical6117 hH).trans (sound228 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix902 (2 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix902 (2 : Fin 3) = raw6051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix902 raw6051; decide +kernel
    rw [heq]
    exact (canonical6051 hH).trans (sound106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node902 + (injectiveMoment H (mergeFirst pivotMatrix902 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix902 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix902 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value902, value106, value228, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation903 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix903 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

theorem sound903 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node903 = Sparse.eval value903 (momentVector H) := by
  have heq : pivotMatrix903 = (fun u v => node903 (pivotPermutation903 u) v) := by apply Matrix.ext; unfold pivotMatrix903 node903 pivotPermutation903; decide +kernel
  have hmoment : injectiveMoment H node903 = injectiveMoment H pivotMatrix903 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix903 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix903 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix903 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix903 (0 : Fin 3) = raw8279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix903 raw8279; decide +kernel
    rw [heq]
    exact (canonical8279 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix903 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix903 (1 : Fin 3) = raw6116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix903 raw6116; decide +kernel
    rw [heq]
    exact (canonical6116 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix903 (2 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix903 (2 : Fin 3) = raw6051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix903 raw6051; decide +kernel
    rw [heq]
    exact (canonical6051 hH).trans (sound106 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node903 + (injectiveMoment H (mergeFirst pivotMatrix903 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix903 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix903 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value903, value106, value146, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation904 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix904 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 1, 1, -3]]

theorem sound904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node904 = Sparse.eval value904 (momentVector H) := by
  have heq : pivotMatrix904 = (fun u v => node904 (pivotPermutation904 u) v) := by apply Matrix.ext; unfold pivotMatrix904 node904 pivotPermutation904; decide +kernel
  have hmoment : injectiveMoment H node904 = injectiveMoment H pivotMatrix904 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix904 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix904 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix904 (0 : Fin 3)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix904 (0 : Fin 3) = raw5999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix904 raw5999; decide +kernel
    rw [heq]
    exact (canonical5999 hH).trans (sound119 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix904 (1 : Fin 3)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix904 (1 : Fin 3) = raw6083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix904 raw6083; decide +kernel
    rw [heq]
    exact (canonical6083 hH).trans (sound253 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix904 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix904 (2 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix904 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node904 + (injectiveMoment H (mergeFirst pivotMatrix904 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix904 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix904 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value904, value119, value145, value253, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation905 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix905 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 1, 0, -2]]

theorem sound905 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node905 = Sparse.eval value905 (momentVector H) := by
  have heq : pivotMatrix905 = (fun u v => node905 (pivotPermutation905 u) v) := by apply Matrix.ext; unfold pivotMatrix905 node905 pivotPermutation905; decide +kernel
  have hmoment : injectiveMoment H node905 = injectiveMoment H pivotMatrix905 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix905 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix905 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix905 (0 : Fin 3)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix905 (0 : Fin 3) = raw6000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix905 raw6000; decide +kernel
    rw [heq]
    exact (canonical6000 hH).trans (sound129 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix905 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix905 (1 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix905 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix905 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix905 (2 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix905 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node905 + (injectiveMoment H (mergeFirst pivotMatrix905 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix905 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix905 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value905, value129, value145, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation906 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix906 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem sound906 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node906 = Sparse.eval value906 (momentVector H) := by
  have heq : pivotMatrix906 = (fun u v => node906 (pivotPermutation906 u) v) := by apply Matrix.ext; unfold pivotMatrix906 node906 pivotPermutation906; decide +kernel
  have hmoment : injectiveMoment H node906 = injectiveMoment H pivotMatrix906 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix906 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix906 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix906 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix906 (0 : Fin 3) = raw6283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix906 raw6283; decide +kernel
    rw [heq]
    exact (canonical6283 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix906 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix906 (1 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix906 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix906 (2 : Fin 3)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix906 (2 : Fin 3) = raw6083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix906 raw6083; decide +kernel
    rw [heq]
    exact (canonical6083 hH).trans (sound253 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node906 + (injectiveMoment H (mergeFirst pivotMatrix906 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix906 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix906 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value906, value145, value253, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation907 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix907 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem sound907 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node907 = Sparse.eval value907 (momentVector H) := by
  have heq : pivotMatrix907 = (fun u v => node907 (pivotPermutation907 u) v) := by apply Matrix.ext; unfold pivotMatrix907 node907 pivotPermutation907; decide +kernel
  have hmoment : injectiveMoment H node907 = injectiveMoment H pivotMatrix907 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix907 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix907 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix907 (0 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix907 (0 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix907 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix907 (1 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix907 (1 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix907 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix907 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix907 (2 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix907 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node907 + (injectiveMoment H (mergeFirst pivotMatrix907 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix907 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix907 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value907, value145, value176, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation908 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix908 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem sound908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node908 = Sparse.eval value908 (momentVector H) := by
  have heq : pivotMatrix908 = (fun u v => node908 (pivotPermutation908 u) v) := by apply Matrix.ext; unfold pivotMatrix908 node908 pivotPermutation908; decide +kernel
  have hmoment : injectiveMoment H node908 = injectiveMoment H pivotMatrix908 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix908 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix908 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix908 (0 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix908 (0 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix908 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix908 (1 : Fin 3)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix908 (1 : Fin 3) = raw6095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix908 raw6095; decide +kernel
    rw [heq]
    exact (canonical6095 hH).trans (sound157 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix908 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix908 (2 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix908 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node908 + (injectiveMoment H (mergeFirst pivotMatrix908 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix908 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix908 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value908, value157, value188, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation909 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix909 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem sound909 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node909 = Sparse.eval value909 (momentVector H) := by
  have heq : pivotMatrix909 = (fun u v => node909 (pivotPermutation909 u) v) := by apply Matrix.ext; unfold pivotMatrix909 node909 pivotPermutation909; decide +kernel
  have hmoment : injectiveMoment H node909 = injectiveMoment H pivotMatrix909 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix909 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix909 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix909 (0 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix909 (0 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix909 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix909 (1 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix909 (1 : Fin 3) = raw6105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix909 raw6105; decide +kernel
    rw [heq]
    exact (canonical6105 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix909 (2 : Fin 3)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix909 (2 : Fin 3) = raw6103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix909 raw6103; decide +kernel
    rw [heq]
    exact (canonical6103 hH).trans (sound270 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node909 + (injectiveMoment H (mergeFirst pivotMatrix909 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix909 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix909 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value909, value254, value270, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation910 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix910 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem sound910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node910 = Sparse.eval value910 (momentVector H) := by
  have heq : pivotMatrix910 = (fun u v => node910 (pivotPermutation910 u) v) := by apply Matrix.ext; unfold pivotMatrix910 node910 pivotPermutation910; decide +kernel
  have hmoment : injectiveMoment H node910 = injectiveMoment H pivotMatrix910 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix910 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix910 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix910 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix910 (0 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix910 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix910 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix910 (1 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix910 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix910 (2 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix910 (2 : Fin 3) = raw6105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix910 raw6105; decide +kernel
    rw [heq]
    exact (canonical6105 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node910 + (injectiveMoment H (mergeFirst pivotMatrix910 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix910 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix910 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value910, value150, value254, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation911 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix911 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem sound911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node911 = Sparse.eval value911 (momentVector H) := by
  have heq : pivotMatrix911 = (fun u v => node911 (pivotPermutation911 u) v) := by apply Matrix.ext; unfold pivotMatrix911 node911 pivotPermutation911; decide +kernel
  have hmoment : injectiveMoment H node911 = injectiveMoment H pivotMatrix911 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix911 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix911 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix911 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix911 (0 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix911 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix911 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix911 (1 : Fin 3) = raw6113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix911 raw6113; decide +kernel
    rw [heq]
    exact (canonical6113 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix911 (2 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix911 (2 : Fin 3) = raw6112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix911 raw6112; decide +kernel
    rw [heq]
    exact (canonical6112 hH).trans (sound228 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node911 + (injectiveMoment H (mergeFirst pivotMatrix911 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix911 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix911 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value911, value146, value228, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation912 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-2, 2, 2, -2], ![4, -2, -2, 0]]

theorem sound912 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node912 = Sparse.eval value912 (momentVector H) := by
  have heq : pivotMatrix912 = (fun u v => node912.transpose (pivotPermutation912 u) v) := by apply Matrix.ext; unfold pivotMatrix912 node912 pivotPermutation912; decide +kernel
  have hmoment : injectiveMoment H node912 = injectiveMoment H pivotMatrix912 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix912 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix912 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix912 (0 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix912 (0 : Fin 3) = raw3288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix912 raw3288; decide +kernel
    rw [heq]
    exact (canonical3288 hH).trans (sound151 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix912 (1 : Fin 3)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix912 (1 : Fin 3) = raw7250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix912 raw7250; decide +kernel
    rw [heq]
    exact (canonical7250 hH).trans (sound256 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix912 (2 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix912 (2 : Fin 3) = raw7254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix912 raw7254; decide +kernel
    rw [heq]
    exact (canonical7254 hH).trans (sound274 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node912 + (injectiveMoment H (mergeFirst pivotMatrix912 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix912 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix912 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value912, value151, value256, value274, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation913 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix913 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-2, 2, -2, 2], ![4, -2, 1, -3]]

theorem sound913 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node913 = Sparse.eval value913 (momentVector H) := by
  have heq : pivotMatrix913 = (fun u v => node913.transpose (pivotPermutation913 u) v) := by apply Matrix.ext; unfold pivotMatrix913 node913 pivotPermutation913; decide +kernel
  have hmoment : injectiveMoment H node913 = injectiveMoment H pivotMatrix913 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix913 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix913 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix913 (0 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix913 (0 : Fin 3) = raw3645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix913 raw3645; decide +kernel
    rw [heq]
    exact (canonical3645 hH).trans (sound152 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix913 (1 : Fin 3)) =
      Sparse.eval value257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix913 (1 : Fin 3) = raw7464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix913 raw7464; decide +kernel
    rw [heq]
    exact (canonical7464 hH).trans (sound257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix913 (2 : Fin 3)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix913 (2 : Fin 3) = raw7468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix913 raw7468; decide +kernel
    rw [heq]
    exact (canonical7468 hH).trans (sound274 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node913 + (injectiveMoment H (mergeFirst pivotMatrix913 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix913 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix913 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value913, value152, value257, value274, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation914 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix914 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

theorem sound914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node914 = Sparse.eval value914 (momentVector H) := by
  have heq : pivotMatrix914 = (fun u v => node914 (pivotPermutation914 u) v) := by apply Matrix.ext; unfold pivotMatrix914 node914 pivotPermutation914; decide +kernel
  have hmoment : injectiveMoment H node914 = injectiveMoment H pivotMatrix914 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix914 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix914 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix914 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix914 (0 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix914 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix914 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix914 (1 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix914 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix914 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix914 (2 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix914 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node914 + (injectiveMoment H (mergeFirst pivotMatrix914 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix914 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix914 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value914, value145, value150, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation915 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix915 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -2, 4], ![0, 0, 2, -2], ![1, 0, 0, -1]]

theorem sound915 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node915 = Sparse.eval value915 (momentVector H) := by
  have heq : pivotMatrix915 = (fun u v => node915 (pivotPermutation915 u) v) := by apply Matrix.ext; unfold pivotMatrix915 node915 pivotPermutation915; decide +kernel
  have hmoment : injectiveMoment H node915 = injectiveMoment H pivotMatrix915 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix915 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix915 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix915 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix915 (0 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix915 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix915 (1 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix915 (1 : Fin 3) = raw6111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix915 raw6111; decide +kernel
    rw [heq]
    exact (canonical6111 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix915 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix915 (2 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix915 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node915 + (injectiveMoment H (mergeFirst pivotMatrix915 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix915 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix915 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value915, value145, value254, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation916 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 2, -2, 2], ![4, -2, 0, -2]]

theorem sound916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node916 = Sparse.eval value916 (momentVector H) := by
  have heq : pivotMatrix916 = (fun u v => node916.transpose (pivotPermutation916 u) v) := by apply Matrix.ext; unfold pivotMatrix916 node916 pivotPermutation916; decide +kernel
  have hmoment : injectiveMoment H node916 = injectiveMoment H pivotMatrix916 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix916 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix916 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix916 (0 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix916 (0 : Fin 3) = raw4165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix916 raw4165; decide +kernel
    rw [heq]
    exact (canonical4165 hH).trans (sound151 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix916 (1 : Fin 3)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix916 (1 : Fin 3) = raw7517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix916 raw7517; decide +kernel
    rw [heq]
    exact (canonical7517 hH).trans (sound211 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix916 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix916 (2 : Fin 3) = raw7522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix916 raw7522; decide +kernel
    rw [heq]
    exact (canonical7522 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node916 + (injectiveMoment H (mergeFirst pivotMatrix916 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix916 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix916 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value916, value151, value211, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation917 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix917 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 2, -1], ![-2, 2, -1, 1], ![4, -2, -1, -1]]

theorem sound917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node917 = Sparse.eval value917 (momentVector H) := by
  have heq : pivotMatrix917 = (fun u v => node917.transpose (pivotPermutation917 u) v) := by apply Matrix.ext; unfold pivotMatrix917 node917 pivotPermutation917; decide +kernel
  have hmoment : injectiveMoment H node917 = injectiveMoment H pivotMatrix917 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix917 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix917 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix917 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix917 (0 : Fin 3) = raw4166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix917 raw4166; decide +kernel
    rw [heq]
    exact (canonical4166 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix917 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix917 (1 : Fin 3) = raw7518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix917 raw7518; decide +kernel
    rw [heq]
    exact (canonical7518 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix917 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix917 (2 : Fin 3) = raw7523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix917 raw7523; decide +kernel
    rw [heq]
    exact (canonical7523 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node917 + (injectiveMoment H (mergeFirst pivotMatrix917 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix917 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix917 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value917, value146, value225, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation918 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix918 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-2, 3, -2, 1], ![4, -3, 1, -2]]

theorem sound918 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node918 = Sparse.eval value918 (momentVector H) := by
  have heq : pivotMatrix918 = (fun u v => node918.transpose (pivotPermutation918 u) v) := by apply Matrix.ext; unfold pivotMatrix918 node918 pivotPermutation918; decide +kernel
  have hmoment : injectiveMoment H node918 = injectiveMoment H pivotMatrix918 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix918 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix918 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix918 (0 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix918 (0 : Fin 3) = raw3647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix918 raw3647; decide +kernel
    rw [heq]
    exact (canonical3647 hH).trans (sound154 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix918 (1 : Fin 3)) =
      Sparse.eval value257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix918 (1 : Fin 3) = raw7465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix918 raw7465; decide +kernel
    rw [heq]
    exact (canonical7465 hH).trans (sound257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix918 (2 : Fin 3)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix918 (2 : Fin 3) = raw7470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix918 raw7470; decide +kernel
    rw [heq]
    exact (canonical7470 hH).trans (sound273 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node918 + (injectiveMoment H (mergeFirst pivotMatrix918 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix918 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix918 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value918, value154, value257, value273, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation919 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix919 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![1, 0, 0, -1]]

theorem sound919 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node919 = Sparse.eval value919 (momentVector H) := by
  have heq : pivotMatrix919 = (fun u v => node919 (pivotPermutation919 u) v) := by apply Matrix.ext; unfold pivotMatrix919 node919 pivotPermutation919; decide +kernel
  have hmoment : injectiveMoment H node919 = injectiveMoment H pivotMatrix919 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix919 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix919 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix919 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix919 (0 : Fin 3) = raw7022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix919 raw7022; decide +kernel
    rw [heq]
    exact (canonical7022 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix919 (1 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix919 (1 : Fin 3) = raw6111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix919 raw6111; decide +kernel
    rw [heq]
    exact (canonical6111 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix919 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix919 (2 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix919 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node919 + (injectiveMoment H (mergeFirst pivotMatrix919 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix919 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix919 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value919, value248, value254, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation920 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix920 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

theorem sound920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node920 = Sparse.eval value920 (momentVector H) := by
  have heq : pivotMatrix920 = (fun u v => node920 (pivotPermutation920 u) v) := by apply Matrix.ext; unfold pivotMatrix920 node920 pivotPermutation920; decide +kernel
  have hmoment : injectiveMoment H node920 = injectiveMoment H pivotMatrix920 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix920 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix920 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix920 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix920 (0 : Fin 3) = raw8023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix920 raw8023; decide +kernel
    rw [heq]
    exact (canonical8023 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix920 (1 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix920 (1 : Fin 3) = raw6117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix920 raw6117; decide +kernel
    rw [heq]
    exact (canonical6117 hH).trans (sound228 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix920 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix920 (2 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix920 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node920 + (injectiveMoment H (mergeFirst pivotMatrix920 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix920 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix920 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value920, value228, value248, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation921 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix921 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem sound921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node921 = Sparse.eval value921 (momentVector H) := by
  have heq : pivotMatrix921 = (fun u v => node921 (pivotPermutation921 u) v) := by apply Matrix.ext; unfold pivotMatrix921 node921 pivotPermutation921; decide +kernel
  have hmoment : injectiveMoment H node921 = injectiveMoment H pivotMatrix921 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix921 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix921 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix921 (0 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix921 (0 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix921 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix921 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix921 (1 : Fin 3) = raw6113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix921 raw6113; decide +kernel
    rw [heq]
    exact (canonical6113 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix921 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix921 (2 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix921 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node921 + (injectiveMoment H (mergeFirst pivotMatrix921 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix921 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix921 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value921, value146, value149, value150, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation922 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix922 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem sound922 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node922 = Sparse.eval value922 (momentVector H) := by
  have heq : pivotMatrix922 = (fun u v => node922 (pivotPermutation922 u) v) := by apply Matrix.ext; unfold pivotMatrix922 node922 pivotPermutation922; decide +kernel
  have hmoment : injectiveMoment H node922 = injectiveMoment H pivotMatrix922 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix922 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix922 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix922 (0 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix922 (0 : Fin 3) = raw7035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix922 raw7035; decide +kernel
    rw [heq]
    exact (canonical7035 hH).trans (sound243 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix922 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix922 (1 : Fin 3) = raw6114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix922 raw6114; decide +kernel
    rw [heq]
    exact (canonical6114 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix922 (2 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix922 (2 : Fin 3) = raw6111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix922 raw6111; decide +kernel
    rw [heq]
    exact (canonical6111 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node922 + (injectiveMoment H (mergeFirst pivotMatrix922 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix922 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix922 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value922, value243, value246, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation923 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix923 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-2, 1, 2, -1], ![4, -2, -3, 1]]

theorem sound923 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node923 = Sparse.eval value923 (momentVector H) := by
  have heq : pivotMatrix923 = (fun u v => node923.transpose (pivotPermutation923 u) v) := by apply Matrix.ext; unfold pivotMatrix923 node923 pivotPermutation923; decide +kernel
  have hmoment : injectiveMoment H node923 = injectiveMoment H pivotMatrix923 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix923 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix923 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix923 (0 : Fin 3)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix923 (0 : Fin 3) = raw4970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix923 raw4970; decide +kernel
    rw [heq]
    exact (canonical4970 hH).trans (sound144 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix923 (1 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix923 (1 : Fin 3) = raw7903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix923 raw7903; decide +kernel
    rw [heq]
    exact (canonical7903 hH).trans (sound241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix923 (2 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix923 (2 : Fin 3) = raw7908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix923 raw7908; decide +kernel
    rw [heq]
    exact (canonical7908 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node923 + (injectiveMoment H (mergeFirst pivotMatrix923 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix923 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix923 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value923, value144, value241, value258, Sparse.eval] at hc ⊢
  linarith

theorem sound924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node924 = Sparse.eval value924 (momentVector H) := by
  have hc : momentVector H 239 = injectiveMoment H node924 := rfl
  simp [value924, Sparse.eval, hc]

theorem sound925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node925 = Sparse.eval value925 (momentVector H) := by
  have hc : momentVector H 870 = injectiveMoment H node925 := rfl
  simp [value925, Sparse.eval, hc]

theorem sound926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node926 = Sparse.eval value926 (momentVector H) := by
  have hc : momentVector H 57 = injectiveMoment H node926 := rfl
  simp [value926, Sparse.eval, hc]

def pivotPermutation927 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![-1, 1, 2, -2], ![3, 1, -4, 0]]

theorem sound927 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node927 = Sparse.eval value927 (momentVector H) := by
  have heq : pivotMatrix927 = (fun u v => node927.transpose (pivotPermutation927 u) v) := by apply Matrix.ext; unfold pivotMatrix927 node927 pivotPermutation927; decide +kernel
  have hmoment : injectiveMoment H node927 = injectiveMoment H pivotMatrix927 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix927 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix927 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix927 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix927 (0 : Fin 3) = raw1272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix927 raw1272; decide +kernel
    rw [heq]
    exact (canonical1272 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix927 (1 : Fin 3)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix927 (1 : Fin 3) = raw5812 := by apply Matrix.ext; unfold mergeFirst pivotMatrix927 raw5812; decide +kernel
    rw [heq]
    exact (canonical5812 hH).trans (sound132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix927 (2 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix927 (2 : Fin 3) = raw5818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix927 raw5818; decide +kernel
    rw [heq]
    exact (canonical5818 hH).trans (sound134 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node927 + (injectiveMoment H (mergeFirst pivotMatrix927 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix927 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix927 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value927, value132, value134, value135, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation928 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 2, 1], ![-1, 2, 1, -2], ![3, 0, -3, 0]]

theorem sound928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node928 = Sparse.eval value928 (momentVector H) := by
  have heq : pivotMatrix928 = (fun u v => node928.transpose (pivotPermutation928 u) v) := by apply Matrix.ext; unfold pivotMatrix928 node928 pivotPermutation928; decide +kernel
  have hmoment : injectiveMoment H node928 = injectiveMoment H pivotMatrix928 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix928 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix928 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix928 (0 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix928 (0 : Fin 3) = raw1273 := by apply Matrix.ext; unfold mergeFirst pivotMatrix928 raw1273; decide +kernel
    rw [heq]
    exact (canonical1273 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix928 (1 : Fin 3)) =
      Sparse.eval value105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix928 (1 : Fin 3) = raw5814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix928 raw5814; decide +kernel
    rw [heq]
    exact (canonical5814 hH).trans (sound105 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix928 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix928 (2 : Fin 3) = raw5819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix928 raw5819; decide +kernel
    rw [heq]
    exact (canonical5819 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node928 + (injectiveMoment H (mergeFirst pivotMatrix928 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix928 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix928 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value928, value101, value105, value111, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation929 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -2, 3, 0], ![-1, 2, 1, -2], ![3, 0, -4, 1]]

theorem sound929 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node929 = Sparse.eval value929 (momentVector H) := by
  have heq : pivotMatrix929 = (fun u v => node929.transpose (pivotPermutation929 u) v) := by apply Matrix.ext; unfold pivotMatrix929 node929 pivotPermutation929; decide +kernel
  have hmoment : injectiveMoment H node929 = injectiveMoment H pivotMatrix929 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix929 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix929 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix929 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix929 (0 : Fin 3) = raw1333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix929 raw1333; decide +kernel
    rw [heq]
    exact (canonical1333 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix929 (1 : Fin 3)) =
      Sparse.eval value83 (momentVector H) := by
    have heq : mergeFirst pivotMatrix929 (1 : Fin 3) = raw5991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix929 raw5991; decide +kernel
    rw [heq]
    exact (canonical5991 hH).trans (sound83 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix929 (2 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix929 (2 : Fin 3) = raw5992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix929 raw5992; decide +kernel
    rw [heq]
    exact (canonical5992 hH).trans (sound85 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node929 + (injectiveMoment H (mergeFirst pivotMatrix929 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix929 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix929 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value929, value191, value83, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation930 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 1, 1], ![3, 2, -2, -3]]

theorem sound930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node930 = Sparse.eval value930 (momentVector H) := by
  have heq : pivotMatrix930 = (fun u v => node930.transpose (pivotPermutation930 u) v) := by apply Matrix.ext; unfold pivotMatrix930 node930 pivotPermutation930; decide +kernel
  have hmoment : injectiveMoment H node930 = injectiveMoment H pivotMatrix930 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix930 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix930 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix930 (0 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix930 (0 : Fin 3) = raw2141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix930 raw2141; decide +kernel
    rw [heq]
    exact (canonical2141 hH).trans (sound258 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix930 (1 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix930 (1 : Fin 3) = raw6572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix930 raw6572; decide +kernel
    rw [heq]
    exact (canonical6572 hH).trans (sound258 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix930 (2 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix930 (2 : Fin 3) = raw6586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix930 raw6586; decide +kernel
    rw [heq]
    exact (canonical6586 hH).trans (sound275 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node930 + (injectiveMoment H (mergeFirst pivotMatrix930 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix930 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix930 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value930, value258, value275, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation931 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, -1, 2, 0], ![3, 2, -3, -2]]

theorem sound931 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node931 = Sparse.eval value931 (momentVector H) := by
  have heq : pivotMatrix931 = (fun u v => node931.transpose (pivotPermutation931 u) v) := by apply Matrix.ext; unfold pivotMatrix931 node931 pivotPermutation931; decide +kernel
  have hmoment : injectiveMoment H node931 = injectiveMoment H pivotMatrix931 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix931 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix931 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix931 (0 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix931 (0 : Fin 3) = raw2144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix931 raw2144; decide +kernel
    rw [heq]
    exact (canonical2144 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix931 (1 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix931 (1 : Fin 3) = raw6573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix931 raw6573; decide +kernel
    rw [heq]
    exact (canonical6573 hH).trans (sound258 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix931 (2 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix931 (2 : Fin 3) = raw6587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix931 raw6587; decide +kernel
    rw [heq]
    exact (canonical6587 hH).trans (sound175 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node931 + (injectiveMoment H (mergeFirst pivotMatrix931 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix931 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix931 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value931, value167, value175, value258, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation932 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, -1, -1, 3], ![3, 2, -1, -4]]

theorem sound932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node932 = Sparse.eval value932 (momentVector H) := by
  have heq : pivotMatrix932 = (fun u v => node932.transpose (pivotPermutation932 u) v) := by apply Matrix.ext; unfold pivotMatrix932 node932 pivotPermutation932; decide +kernel
  have hmoment : injectiveMoment H node932 = injectiveMoment H pivotMatrix932 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix932 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix932 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix932 (0 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix932 (0 : Fin 3) = raw2527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix932 raw2527; decide +kernel
    rw [heq]
    exact (canonical2527 hH).trans (sound89 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix932 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix932 (1 : Fin 3) = raw6892 := by apply Matrix.ext; unfold mergeFirst pivotMatrix932 raw6892; decide +kernel
    rw [heq]
    exact (canonical6892 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix932 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix932 (2 : Fin 3) = raw6903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix932 raw6903; decide +kernel
    rw [heq]
    exact (canonical6903 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node932 + (injectiveMoment H (mergeFirst pivotMatrix932 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix932 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix932 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value932, value219, value223, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation933 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix933 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem sound933 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node933 = Sparse.eval value933 (momentVector H) := by
  have heq : pivotMatrix933 = (fun u v => node933 (pivotPermutation933 u) v) := by apply Matrix.ext; unfold pivotMatrix933 node933 pivotPermutation933; decide +kernel
  have hmoment : injectiveMoment H node933 = injectiveMoment H pivotMatrix933 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix933 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix933 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix933 (0 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix933 (0 : Fin 3) = raw5633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix933 raw5633; decide +kernel
    rw [heq]
    exact (canonical5633 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix933 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix933 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix933 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix933 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix933 (2 : Fin 3) = raw6328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix933 raw6328; decide +kernel
    rw [heq]
    exact (canonical6328 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node933 + (injectiveMoment H (mergeFirst pivotMatrix933 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix933 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix933 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value933, value176, value246, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation934 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix934 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem sound934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node934 = Sparse.eval value934 (momentVector H) := by
  have heq : pivotMatrix934 = (fun u v => node934 (pivotPermutation934 u) v) := by apply Matrix.ext; unfold pivotMatrix934 node934 pivotPermutation934; decide +kernel
  have hmoment : injectiveMoment H node934 = injectiveMoment H pivotMatrix934 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix934 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix934 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix934 (0 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix934 (0 : Fin 3) = raw5634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix934 raw5634; decide +kernel
    rw [heq]
    exact (canonical5634 hH).trans (sound190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix934 (1 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix934 (1 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix934 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix934 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix934 (2 : Fin 3) = raw6329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix934 raw6329; decide +kernel
    rw [heq]
    exact (canonical6329 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node934 + (injectiveMoment H (mergeFirst pivotMatrix934 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix934 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix934 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value934, value173, value188, value190, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation935 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix935 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem sound935 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node935 = Sparse.eval value935 (momentVector H) := by
  have heq : pivotMatrix935 = (fun u v => node935 (pivotPermutation935 u) v) := by apply Matrix.ext; unfold pivotMatrix935 node935 pivotPermutation935; decide +kernel
  have hmoment : injectiveMoment H node935 = injectiveMoment H pivotMatrix935 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix935 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix935 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix935 (0 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix935 (0 : Fin 3) = raw5635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix935 raw5635; decide +kernel
    rw [heq]
    exact (canonical5635 hH).trans (sound171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix935 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix935 (1 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix935 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix935 (2 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix935 (2 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix935 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node935 + (injectiveMoment H (mergeFirst pivotMatrix935 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix935 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix935 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value935, value170, value171, value173, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation936 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix936 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem sound936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node936 = Sparse.eval value936 (momentVector H) := by
  have heq : pivotMatrix936 = (fun u v => node936 (pivotPermutation936 u) v) := by apply Matrix.ext; unfold pivotMatrix936 node936 pivotPermutation936; decide +kernel
  have hmoment : injectiveMoment H node936 = injectiveMoment H pivotMatrix936 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix936 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix936 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix936 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix936 (0 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix936 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix936 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix936 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix936 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix936 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix936 (2 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix936 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node936 + (injectiveMoment H (mergeFirst pivotMatrix936 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix936 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix936 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value936, value176, value181, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation937 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix937 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem sound937 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node937 = Sparse.eval value937 (momentVector H) := by
  have heq : pivotMatrix937 = (fun u v => node937 (pivotPermutation937 u) v) := by apply Matrix.ext; unfold pivotMatrix937 node937 pivotPermutation937; decide +kernel
  have hmoment : injectiveMoment H node937 = injectiveMoment H pivotMatrix937 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix937 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix937 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix937 (0 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix937 (0 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix937 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix937 (1 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix937 (1 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix937 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix937 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix937 (2 : Fin 3) = raw6328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix937 raw6328; decide +kernel
    rw [heq]
    exact (canonical6328 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node937 + (injectiveMoment H (mergeFirst pivotMatrix937 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix937 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix937 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value937, value188, value215, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation938 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix938 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem sound938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node938 = Sparse.eval value938 (momentVector H) := by
  have heq : pivotMatrix938 = (fun u v => node938 (pivotPermutation938 u) v) := by apply Matrix.ext; unfold pivotMatrix938 node938 pivotPermutation938; decide +kernel
  have hmoment : injectiveMoment H node938 = injectiveMoment H pivotMatrix938 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix938 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix938 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix938 (0 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix938 (0 : Fin 3) = raw5724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix938 raw5724; decide +kernel
    rw [heq]
    exact (canonical5724 hH).trans (sound204 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix938 (1 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix938 (1 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix938 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix938 (2 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix938 (2 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix938 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node938 + (injectiveMoment H (mergeFirst pivotMatrix938 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix938 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix938 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value938, value170, value204, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation939 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix939 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node939 = Sparse.eval value939 (momentVector H) := by
  have heq : pivotMatrix939 = (fun u v => node939 (pivotPermutation939 u) v) := by apply Matrix.ext; unfold pivotMatrix939 node939 pivotPermutation939; decide +kernel
  have hmoment : injectiveMoment H node939 = injectiveMoment H pivotMatrix939 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix939 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix939 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix939 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix939 (0 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix939 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix939 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix939 (1 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix939 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix939 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix939 (2 : Fin 3) = raw6331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix939 raw6331; decide +kernel
    rw [heq]
    exact (canonical6331 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node939 + (injectiveMoment H (mergeFirst pivotMatrix939 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix939 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix939 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value939, value185, value229, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation940 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix940 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem sound940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node940 = Sparse.eval value940 (momentVector H) := by
  have heq : pivotMatrix940 = (fun u v => node940 (pivotPermutation940 u) v) := by apply Matrix.ext; unfold pivotMatrix940 node940 pivotPermutation940; decide +kernel
  have hmoment : injectiveMoment H node940 = injectiveMoment H pivotMatrix940 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix940 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix940 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix940 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix940 (0 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix940 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix940 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix940 (1 : Fin 3) = raw6329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix940 raw6329; decide +kernel
    rw [heq]
    exact (canonical6329 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix940 (2 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix940 (2 : Fin 3) = raw6333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix940 raw6333; decide +kernel
    rw [heq]
    exact (canonical6333 hH).trans (sound244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node940 + (injectiveMoment H (mergeFirst pivotMatrix940 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix940 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix940 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value940, value173, value201, value244, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation941 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix941 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, 2, -2, 1], ![3, -1, 1, -3]]

theorem sound941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node941 = Sparse.eval value941 (momentVector H) := by
  have heq : pivotMatrix941 = (fun u v => node941.transpose (pivotPermutation941 u) v) := by apply Matrix.ext; unfold pivotMatrix941 node941 pivotPermutation941; decide +kernel
  have hmoment : injectiveMoment H node941 = injectiveMoment H pivotMatrix941 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix941 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix941 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix941 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix941 (0 : Fin 3) = raw2145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix941 raw2145; decide +kernel
    rw [heq]
    exact (canonical2145 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix941 (1 : Fin 3)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix941 (1 : Fin 3) = raw6574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix941 raw6574; decide +kernel
    rw [heq]
    exact (canonical6574 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix941 (2 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix941 (2 : Fin 3) = raw6591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix941 raw6591; decide +kernel
    rw [heq]
    exact (canonical6591 hH).trans (sound276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node941 + (injectiveMoment H (mergeFirst pivotMatrix941 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix941 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix941 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value941, value159, value260, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation942 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix942 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![1, 1, -1, -1]]

theorem sound942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node942 = Sparse.eval value942 (momentVector H) := by
  have heq : pivotMatrix942 = (fun u v => node942 (pivotPermutation942 u) v) := by apply Matrix.ext; unfold pivotMatrix942 node942 pivotPermutation942; decide +kernel
  have hmoment : injectiveMoment H node942 = injectiveMoment H pivotMatrix942 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix942 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix942 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix942 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (0 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix942 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix942 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node942 + (injectiveMoment H (mergeFirst pivotMatrix942 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix942 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix942 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value942, value176, value229, value230, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation943 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix943 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, 2, 1, -2], ![3, -1, -2, 0]]

theorem sound943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node943 = Sparse.eval value943 (momentVector H) := by
  have heq : pivotMatrix943 = (fun u v => node943.transpose (pivotPermutation943 u) v) := by apply Matrix.ext; unfold pivotMatrix943 node943 pivotPermutation943; decide +kernel
  have hmoment : injectiveMoment H node943 = injectiveMoment H pivotMatrix943 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix943 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix943 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix943 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix943 (0 : Fin 3) = raw2146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix943 raw2146; decide +kernel
    rw [heq]
    exact (canonical2146 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix943 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix943 (1 : Fin 3) = raw6575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix943 raw6575; decide +kernel
    rw [heq]
    exact (canonical6575 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix943 (2 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix943 (2 : Fin 3) = raw6592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix943 raw6592; decide +kernel
    rw [heq]
    exact (canonical6592 hH).trans (sound276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node943 + (injectiveMoment H (mergeFirst pivotMatrix943 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix943 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix943 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value943, value111, value261, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation944 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix944 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 2, -2, 1], ![3, -1, 0, -2]]

theorem sound944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node944 = Sparse.eval value944 (momentVector H) := by
  have heq : pivotMatrix944 = (fun u v => node944.transpose (pivotPermutation944 u) v) := by apply Matrix.ext; unfold pivotMatrix944 node944 pivotPermutation944; decide +kernel
  have hmoment : injectiveMoment H node944 = injectiveMoment H pivotMatrix944 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix944 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix944 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix944 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix944 (0 : Fin 3) = raw2528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix944 raw2528; decide +kernel
    rw [heq]
    exact (canonical2528 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix944 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix944 (1 : Fin 3) = raw6894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix944 raw6894; decide +kernel
    rw [heq]
    exact (canonical6894 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix944 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix944 (2 : Fin 3) = raw6906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix944 raw6906; decide +kernel
    rw [heq]
    exact (canonical6906 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node944 + (injectiveMoment H (mergeFirst pivotMatrix944 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix944 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix944 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value944, value111, value210, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation945 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix945 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1]]

theorem sound945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node945 = Sparse.eval value945 (momentVector H) := by
  have heq : pivotMatrix945 = (fun u v => node945 (pivotPermutation945 u) v) := by apply Matrix.ext; unfold pivotMatrix945 node945 pivotPermutation945; decide +kernel
  have hmoment : injectiveMoment H node945 = injectiveMoment H pivotMatrix945 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix945 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix945 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix945 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (0 : Fin 3) = raw8316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw8316; decide +kernel
    rw [heq]
    exact (canonical8316 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix945 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (1 : Fin 3) = raw6335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw6335; decide +kernel
    rw [heq]
    exact (canonical6335 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix945 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node945 + (injectiveMoment H (mergeFirst pivotMatrix945 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix945 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix945 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value945, value229, value44, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation946 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix946 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2]]

theorem sound946 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node946 = Sparse.eval value946 (momentVector H) := by
  have heq : pivotMatrix946 = (fun u v => node946 (pivotPermutation946 u) v) := by apply Matrix.ext; unfold pivotMatrix946 node946 pivotPermutation946; decide +kernel
  have hmoment : injectiveMoment H node946 = injectiveMoment H pivotMatrix946 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix946 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix946 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix946 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix946 (0 : Fin 3) = raw8295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix946 raw8295; decide +kernel
    rw [heq]
    exact (canonical8295 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix946 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix946 (1 : Fin 3) = raw6334 := by apply Matrix.ext; unfold mergeFirst pivotMatrix946 raw6334; decide +kernel
    rw [heq]
    exact (canonical6334 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix946 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix946 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix946 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node946 + (injectiveMoment H (mergeFirst pivotMatrix946 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix946 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix946 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value946, value176, value229, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation947 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix947 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 2, 1, -2], ![3, -1, -3, 1]]

theorem sound947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node947 = Sparse.eval value947 (momentVector H) := by
  have heq : pivotMatrix947 = (fun u v => node947.transpose (pivotPermutation947 u) v) := by apply Matrix.ext; unfold pivotMatrix947 node947 pivotPermutation947; decide +kernel
  have hmoment : injectiveMoment H node947 = injectiveMoment H pivotMatrix947 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix947 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix947 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix947 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix947 (0 : Fin 3) = raw2529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix947 raw2529; decide +kernel
    rw [heq]
    exact (canonical2529 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix947 (1 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix947 (1 : Fin 3) = raw6896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix947 raw6896; decide +kernel
    rw [heq]
    exact (canonical6896 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix947 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix947 (2 : Fin 3) = raw6908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix947 raw6908; decide +kernel
    rw [heq]
    exact (canonical6908 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node947 + (injectiveMoment H (mergeFirst pivotMatrix947 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix947 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix947 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value947, value159, value180, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation948 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix948 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-1, 3, -2, 0], ![3, -2, 1, -2]]

theorem sound948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node948 = Sparse.eval value948 (momentVector H) := by
  have heq : pivotMatrix948 = (fun u v => node948.transpose (pivotPermutation948 u) v) := by apply Matrix.ext; unfold pivotMatrix948 node948 pivotPermutation948; decide +kernel
  have hmoment : injectiveMoment H node948 = injectiveMoment H pivotMatrix948 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix948 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix948 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix948 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix948 (0 : Fin 3) = raw2147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix948 raw2147; decide +kernel
    rw [heq]
    exact (canonical2147 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix948 (1 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix948 (1 : Fin 3) = raw6576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix948 raw6576; decide +kernel
    rw [heq]
    exact (canonical6576 hH).trans (sound262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix948 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix948 (2 : Fin 3) = raw6594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix948 raw6594; decide +kernel
    rw [heq]
    exact (canonical6594 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node948 + (injectiveMoment H (mergeFirst pivotMatrix948 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix948 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix948 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value948, value103, value261, value262, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation949 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix949 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![1, 1, -1, -1]]

theorem sound949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node949 = Sparse.eval value949 (momentVector H) := by
  have heq : pivotMatrix949 = (fun u v => node949 (pivotPermutation949 u) v) := by apply Matrix.ext; unfold pivotMatrix949 node949 pivotPermutation949; decide +kernel
  have hmoment : injectiveMoment H node949 = injectiveMoment H pivotMatrix949 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix949 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix949 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix949 (0 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix949 (0 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix949 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix949 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix949 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix949 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix949 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix949 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix949 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node949 + (injectiveMoment H (mergeFirst pivotMatrix949 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix949 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix949 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value949, value109, value176, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation950 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix950 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![1, 1, -2, 0]]

theorem sound950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node950 = Sparse.eval value950 (momentVector H) := by
  have heq : pivotMatrix950 = (fun u v => node950 (pivotPermutation950 u) v) := by apply Matrix.ext; unfold pivotMatrix950 node950 pivotPermutation950; decide +kernel
  have hmoment : injectiveMoment H node950 = injectiveMoment H pivotMatrix950 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix950 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix950 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix950 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix950 (0 : Fin 3) = raw7186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix950 raw7186; decide +kernel
    rw [heq]
    exact (canonical7186 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix950 (1 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix950 (1 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix950 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix950 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix950 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix950 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node950 + (injectiveMoment H (mergeFirst pivotMatrix950 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix950 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix950 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value950, value109, value185, value188, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation951 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix951 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0]]

theorem sound951 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node951 = Sparse.eval value951 (momentVector H) := by
  have heq : pivotMatrix951 = (fun u v => node951 (pivotPermutation951 u) v) := by apply Matrix.ext; unfold pivotMatrix951 node951 pivotPermutation951; decide +kernel
  have hmoment : injectiveMoment H node951 = injectiveMoment H pivotMatrix951 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix951 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix951 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix951 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix951 (0 : Fin 3) = raw8317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix951 raw8317; decide +kernel
    rw [heq]
    exact (canonical8317 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix951 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix951 (1 : Fin 3) = raw6336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix951 raw6336; decide +kernel
    rw [heq]
    exact (canonical6336 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix951 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix951 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix951 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node951 + (injectiveMoment H (mergeFirst pivotMatrix951 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix951 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix951 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value951, value109, value170, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation952 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix952 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

theorem sound952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node952 = Sparse.eval value952 (momentVector H) := by
  have heq : pivotMatrix952 = (fun u v => node952 (pivotPermutation952 u) v) := by apply Matrix.ext; unfold pivotMatrix952 node952 pivotPermutation952; decide +kernel
  have hmoment : injectiveMoment H node952 = injectiveMoment H pivotMatrix952 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix952 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix952 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix952 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix952 (0 : Fin 3) = raw8296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix952 raw8296; decide +kernel
    rw [heq]
    exact (canonical8296 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix952 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix952 (1 : Fin 3) = raw6335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix952 raw6335; decide +kernel
    rw [heq]
    exact (canonical6335 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix952 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix952 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix952 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node952 + (injectiveMoment H (mergeFirst pivotMatrix952 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix952 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix952 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value952, value109, value229, value43, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation953 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix953 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 3, 0, -2], ![3, -2, -2, 1]]

theorem sound953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node953 = Sparse.eval value953 (momentVector H) := by
  have heq : pivotMatrix953 = (fun u v => node953.transpose (pivotPermutation953 u) v) := by apply Matrix.ext; unfold pivotMatrix953 node953 pivotPermutation953; decide +kernel
  have hmoment : injectiveMoment H node953 = injectiveMoment H pivotMatrix953 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix953 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix953 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix953 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix953 (0 : Fin 3) = raw2530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix953 raw2530; decide +kernel
    rw [heq]
    exact (canonical2530 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix953 (1 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix953 (1 : Fin 3) = raw6898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix953 raw6898; decide +kernel
    rw [heq]
    exact (canonical6898 hH).trans (sound209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix953 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix953 (2 : Fin 3) = raw6911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix953 raw6911; decide +kernel
    rw [heq]
    exact (canonical6911 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node953 + (injectiveMoment H (mergeFirst pivotMatrix953 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix953 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix953 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value953, value103, value209, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation954 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix954 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 4, -1, -2], ![3, -3, -1, 1]]

theorem sound954 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node954 = Sparse.eval value954 (momentVector H) := by
  have heq : pivotMatrix954 = (fun u v => node954.transpose (pivotPermutation954 u) v) := by apply Matrix.ext; unfold pivotMatrix954 node954 pivotPermutation954; decide +kernel
  have hmoment : injectiveMoment H node954 = injectiveMoment H pivotMatrix954 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix954 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix954 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix954 (0 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix954 (0 : Fin 3) = raw2531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix954 raw2531; decide +kernel
    rw [heq]
    exact (canonical2531 hH).trans (sound161 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix954 (1 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix954 (1 : Fin 3) = raw6899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix954 raw6899; decide +kernel
    rw [heq]
    exact (canonical6899 hH).trans (sound228 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix954 (2 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix954 (2 : Fin 3) = raw6912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix954 raw6912; decide +kernel
    rw [heq]
    exact (canonical6912 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node954 + (injectiveMoment H (mergeFirst pivotMatrix954 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix954 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix954 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value954, value161, value225, value228, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation955 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix955 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, -2, 2, 1], ![3, 2, -2, -3]]

theorem sound955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node955 = Sparse.eval value955 (momentVector H) := by
  have heq : pivotMatrix955 = (fun u v => node955.transpose (pivotPermutation955 u) v) := by apply Matrix.ext; unfold pivotMatrix955 node955 pivotPermutation955; decide +kernel
  have hmoment : injectiveMoment H node955 = injectiveMoment H pivotMatrix955 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix955 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix955 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix955 (0 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix955 (0 : Fin 3) = raw3289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix955 raw3289; decide +kernel
    rw [heq]
    exact (canonical3289 hH).trans (sound162 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix955 (1 : Fin 3)) =
      Sparse.eval value264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix955 (1 : Fin 3) = raw7251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix955 raw7251; decide +kernel
    rw [heq]
    exact (canonical7251 hH).trans (sound264 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix955 (2 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix955 (2 : Fin 3) = raw7257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix955 raw7257; decide +kernel
    rw [heq]
    exact (canonical7257 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node955 + (injectiveMoment H (mergeFirst pivotMatrix955 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix955 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix955 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value955, value162, value264, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation956 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix956 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, -2, 3, 0], ![3, 2, -3, -2]]

theorem sound956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node956 = Sparse.eval value956 (momentVector H) := by
  have heq : pivotMatrix956 = (fun u v => node956.transpose (pivotPermutation956 u) v) := by apply Matrix.ext; unfold pivotMatrix956 node956 pivotPermutation956; decide +kernel
  have hmoment : injectiveMoment H node956 = injectiveMoment H pivotMatrix956 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix956 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix956 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix956 (0 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix956 (0 : Fin 3) = raw3290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix956 raw3290; decide +kernel
    rw [heq]
    exact (canonical3290 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix956 (1 : Fin 3)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix956 (1 : Fin 3) = raw7252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix956 raw7252; decide +kernel
    rw [heq]
    exact (canonical7252 hH).trans (sound265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix956 (2 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix956 (2 : Fin 3) = raw7258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix956 raw7258; decide +kernel
    rw [heq]
    exact (canonical7258 hH).trans (sound280 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node956 + (injectiveMoment H (mergeFirst pivotMatrix956 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix956 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix956 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value956, value163, value265, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation957 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix957 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![-1, -2, 4, -1], ![3, 2, -4, -1]]

theorem sound957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node957 = Sparse.eval value957 (momentVector H) := by
  have heq : pivotMatrix957 = (fun u v => node957.transpose (pivotPermutation957 u) v) := by apply Matrix.ext; unfold pivotMatrix957 node957 pivotPermutation957; decide +kernel
  have hmoment : injectiveMoment H node957 = injectiveMoment H pivotMatrix957 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix957 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix957 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix957 (0 : Fin 3)) =
      Sparse.eval value164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix957 (0 : Fin 3) = raw3291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix957 raw3291; decide +kernel
    rw [heq]
    exact (canonical3291 hH).trans (sound164 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix957 (1 : Fin 3)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix957 (1 : Fin 3) = raw7253 := by apply Matrix.ext; unfold mergeFirst pivotMatrix957 raw7253; decide +kernel
    rw [heq]
    exact (canonical7253 hH).trans (sound266 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix957 (2 : Fin 3)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix957 (2 : Fin 3) = raw7259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix957 raw7259; decide +kernel
    rw [heq]
    exact (canonical7259 hH).trans (sound281 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node957 + (injectiveMoment H (mergeFirst pivotMatrix957 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix957 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix957 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value957, value164, value266, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation958 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![-1, -2, 1, 2], ![3, 2, -2, -3]]

theorem sound958 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node958 = Sparse.eval value958 (momentVector H) := by
  have heq : pivotMatrix958 = (fun u v => node958.transpose (pivotPermutation958 u) v) := by apply Matrix.ext; unfold pivotMatrix958 node958 pivotPermutation958; decide +kernel
  have hmoment : injectiveMoment H node958 = injectiveMoment H pivotMatrix958 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix958 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix958 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix958 (0 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix958 (0 : Fin 3) = raw3648 := by apply Matrix.ext; unfold mergeFirst pivotMatrix958 raw3648; decide +kernel
    rw [heq]
    exact (canonical3648 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix958 (1 : Fin 3)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix958 (1 : Fin 3) = raw7467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix958 raw7467; decide +kernel
    rw [heq]
    exact (canonical7467 hH).trans (sound265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix958 (2 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix958 (2 : Fin 3) = raw7473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix958 raw7473; decide +kernel
    rw [heq]
    exact (canonical7473 hH).trans (sound279 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node958 + (injectiveMoment H (mergeFirst pivotMatrix958 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix958 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix958 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value958, value167, value265, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation959 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix959 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, -1, 3], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem sound959 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node959 = Sparse.eval value959 (momentVector H) := by
  have heq : pivotMatrix959 = (fun u v => node959 (pivotPermutation959 u) v) := by apply Matrix.ext; unfold pivotMatrix959 node959 pivotPermutation959; decide +kernel
  have hmoment : injectiveMoment H node959 = injectiveMoment H pivotMatrix959 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix959 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix959 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix959 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix959 (0 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix959 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix959 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix959 (1 : Fin 3) = raw6283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix959 raw6283; decide +kernel
    rw [heq]
    exact (canonical6283 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix959 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix959 (2 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix959 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node959 + (injectiveMoment H (mergeFirst pivotMatrix959 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix959 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix959 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value959, value145, value176, value271, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
