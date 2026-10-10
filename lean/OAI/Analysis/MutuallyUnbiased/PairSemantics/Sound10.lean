import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical125
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation640 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix640 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem sound640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node640 = Sparse.eval value640 (momentVector H) := by
  have heq : pivotMatrix640 = (fun u v => node640 (pivotPermutation640 u) v) := by apply Matrix.ext; unfold pivotMatrix640 node640 pivotPermutation640; decide +kernel
  have hmoment : injectiveMoment H node640 = injectiveMoment H pivotMatrix640 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix640 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix640 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix640 (0 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix640 (0 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix640 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix640 (1 : Fin 4)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix640 (1 : Fin 4) = raw4012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix640 raw4012; decide +kernel
    rw [heq]
    exact (canonical4012 hH).trans (sound196 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix640 (2 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix640 (2 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix640 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix640 (3 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix640 (3 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix640 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node640 + (injectiveMoment H (mergeFirst pivotMatrix640 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix640 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix640 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix640 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value640, value167, value169, value196, value202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation641 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix641 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]

theorem sound641 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node641 = Sparse.eval value641 (momentVector H) := by
  have heq : pivotMatrix641 = (fun u v => node641 (pivotPermutation641 u) v) := by apply Matrix.ext; unfold pivotMatrix641 node641 pivotPermutation641; decide +kernel
  have hmoment : injectiveMoment H node641 = injectiveMoment H pivotMatrix641 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix641 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix641 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix641 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (0 : Fin 4) = raw4915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4915; decide +kernel
    rw [heq]
    exact (canonical4915 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix641 (1 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (1 : Fin 4) = raw4074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4074; decide +kernel
    rw [heq]
    exact (canonical4074 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix641 (2 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (2 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix641 (3 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix641 (3 : Fin 4) = raw4029 := by apply Matrix.ext; unfold mergeFirst pivotMatrix641 raw4029; decide +kernel
    rw [heq]
    exact (canonical4029 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node641 + (injectiveMoment H (mergeFirst pivotMatrix641 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix641 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix641 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix641 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value641, value169, value197, value203, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation642 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix642 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem sound642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node642 = Sparse.eval value642 (momentVector H) := by
  have heq : pivotMatrix642 = (fun u v => node642 (pivotPermutation642 u) v) := by apply Matrix.ext; unfold pivotMatrix642 node642 pivotPermutation642; decide +kernel
  have hmoment : injectiveMoment H node642 = injectiveMoment H pivotMatrix642 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix642 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix642 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix642 (0 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (0 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix642 (1 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (1 : Fin 4) = raw4079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4079; decide +kernel
    rw [heq]
    exact (canonical4079 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix642 (2 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (2 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix642 (3 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (3 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node642 + (injectiveMoment H (mergeFirst pivotMatrix642 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value642, value197, value198, value203, value224, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation643 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix643 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -2, 0]]

theorem sound643 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node643 = Sparse.eval value643 (momentVector H) := by
  have heq : pivotMatrix643 = (fun u v => node643 (pivotPermutation643 u) v) := by apply Matrix.ext; unfold pivotMatrix643 node643 pivotPermutation643; decide +kernel
  have hmoment : injectiveMoment H node643 = injectiveMoment H pivotMatrix643 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix643 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix643 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix643 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (0 : Fin 4) = raw4920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4920; decide +kernel
    rw [heq]
    exact (canonical4920 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix643 (1 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (1 : Fin 4) = raw4082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4082; decide +kernel
    rw [heq]
    exact (canonical4082 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix643 (2 : Fin 4)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (2 : Fin 4) = raw4040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4040; decide +kernel
    rw [heq]
    exact (canonical4040 hH).trans (sound199 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix643 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix643 (3 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix643 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node643 + (injectiveMoment H (mergeFirst pivotMatrix643 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix643 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix643 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix643 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value643, value198, value199, value204, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation644 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix644 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem sound644 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node644 = Sparse.eval value644 (momentVector H) := by
  have heq : pivotMatrix644 = (fun u v => node644 (pivotPermutation644 u) v) := by apply Matrix.ext; unfold pivotMatrix644 node644 pivotPermutation644; decide +kernel
  have hmoment : injectiveMoment H node644 = injectiveMoment H pivotMatrix644 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix644 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix644 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix644 (0 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix644 (0 : Fin 4) = raw4921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix644 raw4921; decide +kernel
    rw [heq]
    exact (canonical4921 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix644 (1 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix644 (1 : Fin 4) = raw4087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix644 raw4087; decide +kernel
    rw [heq]
    exact (canonical4087 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix644 (2 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix644 (2 : Fin 4) = raw4042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix644 raw4042; decide +kernel
    rw [heq]
    exact (canonical4042 hH).trans (sound201 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix644 (3 : Fin 4)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix644 (3 : Fin 4) = raw4041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix644 raw4041; decide +kernel
    rw [heq]
    exact (canonical4041 hH).trans (sound200 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node644 + (injectiveMoment H (mergeFirst pivotMatrix644 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix644 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix644 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix644 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value644, value200, value201, value206, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation645 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix645 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem sound645 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node645 = Sparse.eval value645 (momentVector H) := by
  have heq : pivotMatrix645 = (fun u v => node645 (pivotPermutation645 u) v) := by apply Matrix.ext; unfold pivotMatrix645 node645 pivotPermutation645; decide +kernel
  have hmoment : injectiveMoment H node645 = injectiveMoment H pivotMatrix645 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix645 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix645 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix645 (0 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix645 (0 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix645 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix645 (1 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix645 (1 : Fin 4) = raw4088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix645 raw4088; decide +kernel
    rw [heq]
    exact (canonical4088 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix645 (2 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix645 (2 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix645 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix645 (3 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix645 (3 : Fin 4) = raw4042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix645 raw4042; decide +kernel
    rw [heq]
    exact (canonical4042 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node645 + (injectiveMoment H (mergeFirst pivotMatrix645 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix645 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix645 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix645 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value645, value169, value185, value201, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation646 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix646 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]

theorem sound646 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node646 = Sparse.eval value646 (momentVector H) := by
  have heq : pivotMatrix646 = (fun u v => node646 (pivotPermutation646 u) v) := by apply Matrix.ext; unfold pivotMatrix646 node646 pivotPermutation646; decide +kernel
  have hmoment : injectiveMoment H node646 = injectiveMoment H pivotMatrix646 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix646 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix646 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix646 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (0 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix646 (1 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (1 : Fin 4) = raw4089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4089; decide +kernel
    rw [heq]
    exact (canonical4089 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix646 (2 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (2 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix646 (3 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix646 (3 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix646 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node646 + (injectiveMoment H (mergeFirst pivotMatrix646 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix646 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix646 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix646 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value646, value169, value202, value210, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation647 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix647 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem sound647 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node647 = Sparse.eval value647 (momentVector H) := by
  have heq : pivotMatrix647 = (fun u v => node647 (pivotPermutation647 u) v) := by apply Matrix.ext; unfold pivotMatrix647 node647 pivotPermutation647; decide +kernel
  have hmoment : injectiveMoment H node647 = injectiveMoment H pivotMatrix647 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix647 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix647 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix647 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix647 (0 : Fin 4) = raw6783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix647 raw6783; decide +kernel
    rw [heq]
    exact (canonical6783 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix647 (1 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix647 (1 : Fin 4) = raw4154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix647 raw4154; decide +kernel
    rw [heq]
    exact (canonical4154 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix647 (2 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix647 (2 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix647 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix647 (3 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix647 (3 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix647 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node647 + (injectiveMoment H (mergeFirst pivotMatrix647 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix647 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix647 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix647 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value647, value197, value202, value212, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation648 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix648 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem sound648 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node648 = Sparse.eval value648 (momentVector H) := by
  have heq : pivotMatrix648 = (fun u v => node648 (pivotPermutation648 u) v) := by apply Matrix.ext; unfold pivotMatrix648 node648 pivotPermutation648; decide +kernel
  have hmoment : injectiveMoment H node648 = injectiveMoment H pivotMatrix648 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix648 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix648 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix648 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix648 (0 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix648 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix648 (1 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix648 (1 : Fin 4) = raw4155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix648 raw4155; decide +kernel
    rw [heq]
    exact (canonical4155 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix648 (2 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix648 (2 : Fin 4) = raw4045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix648 raw4045; decide +kernel
    rw [heq]
    exact (canonical4045 hH).trans (sound169 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix648 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix648 (3 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix648 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node648 + (injectiveMoment H (mergeFirst pivotMatrix648 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix648 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix648 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix648 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value648, value169, value198, value214, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation649 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix649 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

theorem sound649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node649 = Sparse.eval value649 (momentVector H) := by
  have heq : pivotMatrix649 = (fun u v => node649 (pivotPermutation649 u) v) := by apply Matrix.ext; unfold pivotMatrix649 node649 pivotPermutation649; decide +kernel
  have hmoment : injectiveMoment H node649 = injectiveMoment H pivotMatrix649 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix649 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix649 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix649 (0 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix649 (0 : Fin 4) = raw7417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix649 raw7417; decide +kernel
    rw [heq]
    exact (canonical7417 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix649 (1 : Fin 4)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix649 (1 : Fin 4) = raw4158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix649 raw4158; decide +kernel
    rw [heq]
    exact (canonical4158 hH).trans (sound218 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix649 (2 : Fin 4)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix649 (2 : Fin 4) = raw4047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix649 raw4047; decide +kernel
    rw [heq]
    exact (canonical4047 hH).trans (sound200 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix649 (3 : Fin 4)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix649 (3 : Fin 4) = raw4040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix649 raw4040; decide +kernel
    rw [heq]
    exact (canonical4040 hH).trans (sound199 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node649 + (injectiveMoment H (mergeFirst pivotMatrix649 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix649 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix649 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix649 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value649, value199, value200, value218, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation650 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix650 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem sound650 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node650 = Sparse.eval value650 (momentVector H) := by
  have heq : pivotMatrix650 = (fun u v => node650 (pivotPermutation650 u) v) := by apply Matrix.ext; unfold pivotMatrix650 node650 pivotPermutation650; decide +kernel
  have hmoment : injectiveMoment H node650 = injectiveMoment H pivotMatrix650 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix650 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix650 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix650 (0 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix650 (0 : Fin 4) = raw6788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix650 raw6788; decide +kernel
    rw [heq]
    exact (canonical6788 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix650 (1 : Fin 4)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix650 (1 : Fin 4) = raw4156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix650 raw4156; decide +kernel
    rw [heq]
    exact (canonical4156 hH).trans (sound217 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix650 (2 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix650 (2 : Fin 4) = raw4046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix650 raw4046; decide +kernel
    rw [heq]
    exact (canonical4046 hH).trans (sound201 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix650 (3 : Fin 4)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix650 (3 : Fin 4) = raw4040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix650 raw4040; decide +kernel
    rw [heq]
    exact (canonical4040 hH).trans (sound199 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node650 + (injectiveMoment H (mergeFirst pivotMatrix650 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix650 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix650 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix650 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value650, value199, value201, value217, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation651 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix651 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem sound651 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node651 = Sparse.eval value651 (momentVector H) := by
  have heq : pivotMatrix651 = (fun u v => node651 (pivotPermutation651 u) v) := by apply Matrix.ext; unfold pivotMatrix651 node651 pivotPermutation651; decide +kernel
  have hmoment : injectiveMoment H node651 = injectiveMoment H pivotMatrix651 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix651 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix651 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix651 (0 : Fin 4)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix651 (0 : Fin 4) = raw2759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix651 raw2759; decide +kernel
    rw [heq]
    exact (canonical2759 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix651 (1 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix651 (1 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix651 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix651 (2 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix651 (2 : Fin 4) = raw4079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix651 raw4079; decide +kernel
    rw [heq]
    exact (canonical4079 hH).trans (sound203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix651 (3 : Fin 4)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix651 (3 : Fin 4) = raw4082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix651 raw4082; decide +kernel
    rw [heq]
    exact (canonical4082 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node651 + (injectiveMoment H (mergeFirst pivotMatrix651 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix651 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix651 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix651 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value651, value170, value198, value203, value204, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation652 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix652 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

theorem sound652 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node652 = Sparse.eval value652 (momentVector H) := by
  have heq : pivotMatrix652 = (fun u v => node652 (pivotPermutation652 u) v) := by apply Matrix.ext; unfold pivotMatrix652 node652 pivotPermutation652; decide +kernel
  have hmoment : injectiveMoment H node652 = injectiveMoment H pivotMatrix652 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix652 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix652 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix652 (0 : Fin 4)) =
      Sparse.eval value172 (momentVector H) := by
    have heq : mergeFirst pivotMatrix652 (0 : Fin 4) = raw2762 := by apply Matrix.ext; unfold mergeFirst pivotMatrix652 raw2762; decide +kernel
    rw [heq]
    exact (canonical2762 hH).trans (sound172 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix652 (1 : Fin 4)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix652 (1 : Fin 4) = raw4041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix652 raw4041; decide +kernel
    rw [heq]
    exact (canonical4041 hH).trans (sound200 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix652 (2 : Fin 4)) =
      Sparse.eval value205 (momentVector H) := by
    have heq : mergeFirst pivotMatrix652 (2 : Fin 4) = raw4086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix652 raw4086; decide +kernel
    rw [heq]
    exact (canonical4086 hH).trans (sound205 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix652 (3 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix652 (3 : Fin 4) = raw4087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix652 raw4087; decide +kernel
    rw [heq]
    exact (canonical4087 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node652 + (injectiveMoment H (mergeFirst pivotMatrix652 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix652 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix652 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix652 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value652, value172, value200, value205, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation653 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix653 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem sound653 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node653 = Sparse.eval value653 (momentVector H) := by
  have heq : pivotMatrix653 = (fun u v => node653 (pivotPermutation653 u) v) := by apply Matrix.ext; unfold pivotMatrix653 node653 pivotPermutation653; decide +kernel
  have hmoment : injectiveMoment H node653 = injectiveMoment H pivotMatrix653 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix653 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix653 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix653 (0 : Fin 4)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix653 (0 : Fin 4) = raw2765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix653 raw2765; decide +kernel
    rw [heq]
    exact (canonical2765 hH).trans (sound173 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix653 (1 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix653 (1 : Fin 4) = raw4042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix653 raw4042; decide +kernel
    rw [heq]
    exact (canonical4042 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix653 (2 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix653 (2 : Fin 4) = raw4087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix653 raw4087; decide +kernel
    rw [heq]
    exact (canonical4087 hH).trans (sound206 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix653 (3 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix653 (3 : Fin 4) = raw4088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix653 raw4088; decide +kernel
    rw [heq]
    exact (canonical4088 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node653 + (injectiveMoment H (mergeFirst pivotMatrix653 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix653 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix653 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix653 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value653, value173, value185, value201, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation654 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix654 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem sound654 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node654 = Sparse.eval value654 (momentVector H) := by
  have heq : pivotMatrix654 = (fun u v => node654 (pivotPermutation654 u) v) := by apply Matrix.ext; unfold pivotMatrix654 node654 pivotPermutation654; decide +kernel
  have hmoment : injectiveMoment H node654 = injectiveMoment H pivotMatrix654 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix654 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix654 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix654 (0 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix654 (0 : Fin 4) = raw2767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix654 raw2767; decide +kernel
    rw [heq]
    exact (canonical2767 hH).trans (sound175 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix654 (1 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix654 (1 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix654 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix654 (2 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix654 (2 : Fin 4) = raw4089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix654 raw4089; decide +kernel
    rw [heq]
    exact (canonical4089 hH).trans (sound284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix654 (3 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix654 (3 : Fin 4) = raw4090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix654 raw4090; decide +kernel
    rw [heq]
    exact (canonical4090 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node654 + (injectiveMoment H (mergeFirst pivotMatrix654 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix654 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix654 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix654 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value654, value175, value202, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation655 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix655 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem sound655 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node655 = Sparse.eval value655 (momentVector H) := by
  have heq : pivotMatrix655 = (fun u v => node655 (pivotPermutation655 u) v) := by apply Matrix.ext; unfold pivotMatrix655 node655 pivotPermutation655; decide +kernel
  have hmoment : injectiveMoment H node655 = injectiveMoment H pivotMatrix655 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix655 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix655 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (0 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (1 : Fin 4) = raw4096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4096; decide +kernel
    rw [heq]
    exact (canonical4096 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (2 : Fin 4) = raw4110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4110; decide +kernel
    rw [heq]
    exact (canonical4110 hH).trans (sound62 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix655 (3 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix655 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node655 + (injectiveMoment H (mergeFirst pivotMatrix655 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix655 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value655, value176, value207, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation656 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix656 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem sound656 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node656 = Sparse.eval value656 (momentVector H) := by
  have heq : pivotMatrix656 = (fun u v => node656 (pivotPermutation656 u) v) := by apply Matrix.ext; unfold pivotMatrix656 node656 pivotPermutation656; decide +kernel
  have hmoment : injectiveMoment H node656 = injectiveMoment H pivotMatrix656 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix656 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix656 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix656 (0 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (0 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix656 (1 : Fin 4)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (1 : Fin 4) = raw4099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw4099; decide +kernel
    rw [heq]
    exact (canonical4099 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix656 (2 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (2 : Fin 4) = raw4117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw4117; decide +kernel
    rw [heq]
    exact (canonical4117 hH).trans (sound207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix656 (3 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix656 (3 : Fin 4) = raw4123 := by apply Matrix.ext; unfold mergeFirst pivotMatrix656 raw4123; decide +kernel
    rw [heq]
    exact (canonical4123 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node656 + (injectiveMoment H (mergeFirst pivotMatrix656 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix656 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix656 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix656 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value656, value177, value207, value41, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation657 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix657 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

theorem sound657 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node657 = Sparse.eval value657 (momentVector H) := by
  have heq : pivotMatrix657 = (fun u v => node657 (pivotPermutation657 u) v) := by apply Matrix.ext; unfold pivotMatrix657 node657 pivotPermutation657; decide +kernel
  have hmoment : injectiveMoment H node657 = injectiveMoment H pivotMatrix657 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix657 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix657 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix657 (0 : Fin 4)) =
      Sparse.eval value179 (momentVector H) := by
    have heq : mergeFirst pivotMatrix657 (0 : Fin 4) = raw2816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix657 raw2816; decide +kernel
    rw [heq]
    exact (canonical2816 hH).trans (sound179 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix657 (1 : Fin 4)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix657 (1 : Fin 4) = raw4101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix657 raw4101; decide +kernel
    rw [heq]
    exact (canonical4101 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix657 (2 : Fin 4)) =
      Sparse.eval value208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix657 (2 : Fin 4) = raw4126 := by apply Matrix.ext; unfold mergeFirst pivotMatrix657 raw4126; decide +kernel
    rw [heq]
    exact (canonical4126 hH).trans (sound208 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix657 (3 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix657 (3 : Fin 4) = raw4127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix657 raw4127; decide +kernel
    rw [heq]
    exact (canonical4127 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node657 + (injectiveMoment H (mergeFirst pivotMatrix657 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix657 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix657 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix657 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value657, value179, value208, value209, value32, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation658 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix658 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem sound658 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node658 = Sparse.eval value658 (momentVector H) := by
  have heq : pivotMatrix658 = (fun u v => node658 (pivotPermutation658 u) v) := by apply Matrix.ext; unfold pivotMatrix658 node658 pivotPermutation658; decide +kernel
  have hmoment : injectiveMoment H node658 = injectiveMoment H pivotMatrix658 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix658 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix658 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix658 (0 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix658 (0 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix658 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix658 (1 : Fin 4)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix658 (1 : Fin 4) = raw4102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix658 raw4102; decide +kernel
    rw [heq]
    exact (canonical4102 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix658 (2 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix658 (2 : Fin 4) = raw4127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix658 raw4127; decide +kernel
    rw [heq]
    exact (canonical4127 hH).trans (sound209 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix658 (3 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix658 (3 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix658 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node658 + (injectiveMoment H (mergeFirst pivotMatrix658 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix658 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix658 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix658 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value658, value180, value209, value210, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation659 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix659 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node659 = Sparse.eval value659 (momentVector H) := by
  have heq : pivotMatrix659 = (fun u v => node659 (pivotPermutation659 u) v) := by apply Matrix.ext; unfold pivotMatrix659 node659 pivotPermutation659; decide +kernel
  have hmoment : injectiveMoment H node659 = injectiveMoment H pivotMatrix659 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix659 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix659 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix659 (0 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (0 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix659 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (1 : Fin 4) = raw4103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw4103; decide +kernel
    rw [heq]
    exact (canonical4103 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix659 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (2 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix659 (3 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (3 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node659 + (injectiveMoment H (mergeFirst pivotMatrix659 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix659 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix659 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix659 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value659, value181, value210, value294, value62, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation660 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix660 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem sound660 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node660 = Sparse.eval value660 (momentVector H) := by
  have heq : pivotMatrix660 = (fun u v => node660 (pivotPermutation660 u) v) := by apply Matrix.ext; unfold pivotMatrix660 node660 pivotPermutation660; decide +kernel
  have hmoment : injectiveMoment H node660 = injectiveMoment H pivotMatrix660 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix660 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix660 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix660 (0 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix660 (0 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix660 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix660 (1 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix660 (1 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix660 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix660 (2 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix660 (2 : Fin 4) = raw4138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix660 raw4138; decide +kernel
    rw [heq]
    exact (canonical4138 hH).trans (sound212 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix660 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix660 (3 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix660 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node660 + (injectiveMoment H (mergeFirst pivotMatrix660 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix660 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix660 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix660 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value660, value184, value203, value210, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation661 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix661 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node661 = Sparse.eval value661 (momentVector H) := by
  have heq : pivotMatrix661 = (fun u v => node661 (pivotPermutation661 u) v) := by apply Matrix.ext; unfold pivotMatrix661 node661 pivotPermutation661; decide +kernel
  have hmoment : injectiveMoment H node661 = injectiveMoment H pivotMatrix661 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix661 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix661 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix661 (0 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix661 (0 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix661 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix661 (1 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix661 (1 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix661 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix661 (2 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix661 (2 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix661 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix661 (3 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix661 (3 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix661 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node661 + (injectiveMoment H (mergeFirst pivotMatrix661 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix661 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix661 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix661 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value661, value185, value203, value207, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation662 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix662 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem sound662 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node662 = Sparse.eval value662 (momentVector H) := by
  have heq : pivotMatrix662 = (fun u v => node662 (pivotPermutation662 u) v) := by apply Matrix.ext; unfold pivotMatrix662 node662 pivotPermutation662; decide +kernel
  have hmoment : injectiveMoment H node662 = injectiveMoment H pivotMatrix662 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix662 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix662 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix662 (0 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix662 (0 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix662 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix662 (1 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix662 (1 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix662 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix662 (2 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix662 (2 : Fin 4) = raw4144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix662 raw4144; decide +kernel
    rw [heq]
    exact (canonical4144 hH).trans (sound214 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix662 (3 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix662 (3 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix662 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node662 + (injectiveMoment H (mergeFirst pivotMatrix662 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix662 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix662 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix662 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value662, value187, value203, value214, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation663 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix663 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem sound663 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node663 = Sparse.eval value663 (momentVector H) := by
  have heq : pivotMatrix663 = (fun u v => node663 (pivotPermutation663 u) v) := by apply Matrix.ext; unfold pivotMatrix663 node663 pivotPermutation663; decide +kernel
  have hmoment : injectiveMoment H node663 = injectiveMoment H pivotMatrix663 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix663 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix663 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix663 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix663 (0 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix663 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix663 (1 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix663 (1 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix663 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix663 (2 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix663 (2 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix663 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix663 (3 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix663 (3 : Fin 4) = raw4146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix663 raw4146; decide +kernel
    rw [heq]
    exact (canonical4146 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node663 + (injectiveMoment H (mergeFirst pivotMatrix663 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix663 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix663 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix663 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value663, value188, value207, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation664 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix664 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

theorem sound664 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node664 = Sparse.eval value664 (momentVector H) := by
  have heq : pivotMatrix664 = (fun u v => node664 (pivotPermutation664 u) v) := by apply Matrix.ext; unfold pivotMatrix664 node664 pivotPermutation664; decide +kernel
  have hmoment : injectiveMoment H node664 = injectiveMoment H pivotMatrix664 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix664 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix664 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix664 (0 : Fin 4)) =
      Sparse.eval value189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix664 (0 : Fin 4) = raw2850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix664 raw2850; decide +kernel
    rw [heq]
    exact (canonical2850 hH).trans (sound189 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix664 (1 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix664 (1 : Fin 4) = raw4144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix664 raw4144; decide +kernel
    rw [heq]
    exact (canonical4144 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix664 (2 : Fin 4)) =
      Sparse.eval value216 (momentVector H) := by
    have heq : mergeFirst pivotMatrix664 (2 : Fin 4) = raw4148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix664 raw4148; decide +kernel
    rw [heq]
    exact (canonical4148 hH).trans (sound216 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix664 (3 : Fin 4)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix664 (3 : Fin 4) = raw4149 := by apply Matrix.ext; unfold mergeFirst pivotMatrix664 raw4149; decide +kernel
    rw [heq]
    exact (canonical4149 hH).trans (sound217 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node664 + (injectiveMoment H (mergeFirst pivotMatrix664 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix664 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix664 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix664 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value664, value189, value214, value216, value217, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation665 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix665 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem sound665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node665 = Sparse.eval value665 (momentVector H) := by
  have heq : pivotMatrix665 = (fun u v => node665 (pivotPermutation665 u) v) := by apply Matrix.ext; unfold pivotMatrix665 node665 pivotPermutation665; decide +kernel
  have hmoment : injectiveMoment H node665 = injectiveMoment H pivotMatrix665 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix665 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix665 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix665 (0 : Fin 4)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix665 (0 : Fin 4) = raw2851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix665 raw2851; decide +kernel
    rw [heq]
    exact (canonical2851 hH).trans (sound190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix665 (1 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix665 (1 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix665 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix665 (2 : Fin 4)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix665 (2 : Fin 4) = raw4149 := by apply Matrix.ext; unfold mergeFirst pivotMatrix665 raw4149; decide +kernel
    rw [heq]
    exact (canonical4149 hH).trans (sound217 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix665 (3 : Fin 4)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix665 (3 : Fin 4) = raw4150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix665 raw4150; decide +kernel
    rw [heq]
    exact (canonical4150 hH).trans (sound218 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node665 + (injectiveMoment H (mergeFirst pivotMatrix665 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix665 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix665 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix665 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value665, value190, value215, value217, value218, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation666 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix666 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem sound666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node666 = Sparse.eval value666 (momentVector H) := by
  have heq : pivotMatrix666 = (fun u v => node666 (pivotPermutation666 u) v) := by apply Matrix.ext; unfold pivotMatrix666 node666 pivotPermutation666; decide +kernel
  have hmoment : injectiveMoment H node666 = injectiveMoment H pivotMatrix666 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix666 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix666 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix666 (0 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix666 (0 : Fin 4) = raw4953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix666 raw4953; decide +kernel
    rw [heq]
    exact (canonical4953 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix666 (1 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix666 (1 : Fin 4) = raw4138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix666 raw4138; decide +kernel
    rw [heq]
    exact (canonical4138 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix666 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix666 (2 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix666 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix666 (3 : Fin 4)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix666 (3 : Fin 4) = raw4127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix666 raw4127; decide +kernel
    rw [heq]
    exact (canonical4127 hH).trans (sound209 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node666 + (injectiveMoment H (mergeFirst pivotMatrix666 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix666 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix666 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix666 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value666, value209, value210, value212, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation667 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix667 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem sound667 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node667 = Sparse.eval value667 (momentVector H) := by
  have heq : pivotMatrix667 = (fun u v => node667 (pivotPermutation667 u) v) := by apply Matrix.ext; unfold pivotMatrix667 node667 pivotPermutation667; decide +kernel
  have hmoment : injectiveMoment H node667 = injectiveMoment H pivotMatrix667 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix667 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix667 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix667 (0 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (0 : Fin 4) = raw4954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4954; decide +kernel
    rw [heq]
    exact (canonical4954 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix667 (1 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (1 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix667 (2 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (2 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix667 (3 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix667 (3 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix667 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node667 + (injectiveMoment H (mergeFirst pivotMatrix667 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix667 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix667 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix667 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value667, value203, value210, value230, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation668 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix668 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem sound668 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node668 = Sparse.eval value668 (momentVector H) := by
  have heq : pivotMatrix668 = (fun u v => node668 (pivotPermutation668 u) v) := by apply Matrix.ext; unfold pivotMatrix668 node668 pivotPermutation668; decide +kernel
  have hmoment : injectiveMoment H node668 = injectiveMoment H pivotMatrix668 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix668 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix668 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix668 (0 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (0 : Fin 4) = raw4955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4955; decide +kernel
    rw [heq]
    exact (canonical4955 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix668 (1 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (1 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix668 (2 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (2 : Fin 4) = raw4133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4133; decide +kernel
    rw [heq]
    exact (canonical4133 hH).trans (sound294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix668 (3 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (3 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node668 + (injectiveMoment H (mergeFirst pivotMatrix668 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix668 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix668 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix668 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value668, value207, value287, value294, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation669 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix669 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem sound669 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node669 = Sparse.eval value669 (momentVector H) := by
  have heq : pivotMatrix669 = (fun u v => node669 (pivotPermutation669 u) v) := by apply Matrix.ext; unfold pivotMatrix669 node669 pivotPermutation669; decide +kernel
  have hmoment : injectiveMoment H node669 = injectiveMoment H pivotMatrix669 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix669 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix669 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix669 (0 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix669 (0 : Fin 4) = raw4957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix669 raw4957; decide +kernel
    rw [heq]
    exact (canonical4957 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix669 (1 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix669 (1 : Fin 4) = raw4144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix669 raw4144; decide +kernel
    rw [heq]
    exact (canonical4144 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix669 (2 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix669 (2 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix669 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix669 (3 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix669 (3 : Fin 4) = raw4138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix669 raw4138; decide +kernel
    rw [heq]
    exact (canonical4138 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node669 + (injectiveMoment H (mergeFirst pivotMatrix669 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix669 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix669 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix669 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value669, value203, value212, value214, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation670 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix670 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem sound670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node670 = Sparse.eval value670 (momentVector H) := by
  have heq : pivotMatrix670 = (fun u v => node670 (pivotPermutation670 u) v) := by apply Matrix.ext; unfold pivotMatrix670 node670 pivotPermutation670; decide +kernel
  have hmoment : injectiveMoment H node670 = injectiveMoment H pivotMatrix670 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix670 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix670 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix670 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (0 : Fin 4) = raw4958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4958; decide +kernel
    rw [heq]
    exact (canonical4958 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix670 (1 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (1 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix670 (2 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (2 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix670 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (3 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node670 + (injectiveMoment H (mergeFirst pivotMatrix670 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value670, value203, value207, value210, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation671 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix671 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

theorem sound671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node671 = Sparse.eval value671 (momentVector H) := by
  have heq : pivotMatrix671 = (fun u v => node671 (pivotPermutation671 u) v) := by apply Matrix.ext; unfold pivotMatrix671 node671 pivotPermutation671; decide +kernel
  have hmoment : injectiveMoment H node671 = injectiveMoment H pivotMatrix671 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix671 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix671 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix671 (0 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix671 (0 : Fin 4) = raw4959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix671 raw4959; decide +kernel
    rw [heq]
    exact (canonical4959 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix671 (1 : Fin 4)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix671 (1 : Fin 4) = raw4149 := by apply Matrix.ext; unfold mergeFirst pivotMatrix671 raw4149; decide +kernel
    rw [heq]
    exact (canonical4149 hH).trans (sound217 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix671 (2 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix671 (2 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix671 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix671 (3 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix671 (3 : Fin 4) = raw4144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix671 raw4144; decide +kernel
    rw [heq]
    exact (canonical4144 hH).trans (sound214 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node671 + (injectiveMoment H (mergeFirst pivotMatrix671 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix671 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix671 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix671 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value671, value214, value215, value217, value222, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation672 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix672 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

theorem sound672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node672 = Sparse.eval value672 (momentVector H) := by
  have heq : pivotMatrix672 = (fun u v => node672 (pivotPermutation672 u) v) := by apply Matrix.ext; unfold pivotMatrix672 node672 pivotPermutation672; decide +kernel
  have hmoment : injectiveMoment H node672 = injectiveMoment H pivotMatrix672 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix672 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix672 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix672 (0 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix672 (0 : Fin 4) = raw4960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix672 raw4960; decide +kernel
    rw [heq]
    exact (canonical4960 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix672 (1 : Fin 4)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix672 (1 : Fin 4) = raw4150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix672 raw4150; decide +kernel
    rw [heq]
    exact (canonical4150 hH).trans (sound218 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix672 (2 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix672 (2 : Fin 4) = raw4146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix672 raw4146; decide +kernel
    rw [heq]
    exact (canonical4146 hH).trans (sound215 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix672 (3 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix672 (3 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix672 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node672 + (injectiveMoment H (mergeFirst pivotMatrix672 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix672 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix672 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix672 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value672, value215, value218, value223, Sparse.eval] at hc ⊢
  linarith

theorem sound673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node673 = Sparse.eval value673 (momentVector H) := by
  have hc : momentVector H 735 = injectiveMoment H node673 := rfl
  simp [value673, Sparse.eval, hc]

theorem sound674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node674 = Sparse.eval value674 (momentVector H) := by
  have hc : momentVector H 736 = injectiveMoment H node674 := rfl
  simp [value674, Sparse.eval, hc]

theorem sound675 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node675 = Sparse.eval value675 (momentVector H) := by
  have hc : momentVector H 737 = injectiveMoment H node675 := rfl
  simp [value675, Sparse.eval, hc]

theorem sound676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node676 = Sparse.eval value676 (momentVector H) := by
  have hc : momentVector H 738 = injectiveMoment H node676 := rfl
  simp [value676, Sparse.eval, hc]

theorem sound677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node677 = Sparse.eval value677 (momentVector H) := by
  have hc : momentVector H 739 = injectiveMoment H node677 := rfl
  simp [value677, Sparse.eval, hc]

theorem sound678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node678 = Sparse.eval value678 (momentVector H) := by
  have hc : momentVector H 203 = injectiveMoment H node678 := rfl
  simp [value678, Sparse.eval, hc]

theorem sound679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node679 = Sparse.eval value679 (momentVector H) := by
  have hc : momentVector H 745 = injectiveMoment H node679 := rfl
  simp [value679, Sparse.eval, hc]

theorem sound680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node680 = Sparse.eval value680 (momentVector H) := by
  have hc : momentVector H 204 = injectiveMoment H node680 := rfl
  simp [value680, Sparse.eval, hc]

theorem sound681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node681 = Sparse.eval value681 (momentVector H) := by
  have hc : momentVector H 751 = injectiveMoment H node681 := rfl
  simp [value681, Sparse.eval, hc]

theorem sound682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node682 = Sparse.eval value682 (momentVector H) := by
  have hc : momentVector H 753 = injectiveMoment H node682 := rfl
  simp [value682, Sparse.eval, hc]

theorem sound683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node683 = Sparse.eval value683 (momentVector H) := by
  have hc : momentVector H 205 = injectiveMoment H node683 := rfl
  simp [value683, Sparse.eval, hc]

theorem sound684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node684 = Sparse.eval value684 (momentVector H) := by
  have hc : momentVector H 207 = injectiveMoment H node684 := rfl
  simp [value684, Sparse.eval, hc]

theorem sound685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node685 = Sparse.eval value685 (momentVector H) := by
  have hc : momentVector H 208 = injectiveMoment H node685 := rfl
  simp [value685, Sparse.eval, hc]

theorem sound686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node686 = Sparse.eval value686 (momentVector H) := by
  have hc : momentVector H 209 = injectiveMoment H node686 := rfl
  simp [value686, Sparse.eval, hc]

theorem sound687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node687 = Sparse.eval value687 (momentVector H) := by
  have hc : momentVector H 760 = injectiveMoment H node687 := rfl
  simp [value687, Sparse.eval, hc]

theorem sound688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node688 = Sparse.eval value688 (momentVector H) := by
  have hc : momentVector H 764 = injectiveMoment H node688 := rfl
  simp [value688, Sparse.eval, hc]

theorem sound689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node689 = Sparse.eval value689 (momentVector H) := by
  have hc : momentVector H 216 = injectiveMoment H node689 := rfl
  simp [value689, Sparse.eval, hc]

theorem sound690 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node690 = Sparse.eval value690 (momentVector H) := by
  have hc : momentVector H 217 = injectiveMoment H node690 := rfl
  simp [value690, Sparse.eval, hc]

theorem sound691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node691 = Sparse.eval value691 (momentVector H) := by
  have hc : momentVector H 783 = injectiveMoment H node691 := rfl
  simp [value691, Sparse.eval, hc]

theorem sound692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node692 = Sparse.eval value692 (momentVector H) := by
  have hc : momentVector H 784 = injectiveMoment H node692 := rfl
  simp [value692, Sparse.eval, hc]

theorem sound693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node693 = Sparse.eval value693 (momentVector H) := by
  have hc : momentVector H 794 = injectiveMoment H node693 := rfl
  simp [value693, Sparse.eval, hc]

def pivotPermutation694 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix694 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 3, -4]]

theorem sound694 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node694 = Sparse.eval value694 (momentVector H) := by
  have heq : pivotMatrix694 = (fun u v => node694 (pivotPermutation694 u) v) := by apply Matrix.ext; unfold pivotMatrix694 node694 pivotPermutation694; decide +kernel
  have hmoment : injectiveMoment H node694 = injectiveMoment H pivotMatrix694 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix694 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix694 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix694 (0 : Fin 4)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix694 (0 : Fin 4) = raw7366 := by apply Matrix.ext; unfold mergeFirst pivotMatrix694 raw7366; decide +kernel
    rw [heq]
    exact (canonical7366 hH).trans (sound243 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix694 (1 : Fin 4)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix694 (1 : Fin 4) = raw4904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix694 raw4904; decide +kernel
    rw [heq]
    exact (canonical4904 hH).trans (sound221 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix694 (2 : Fin 4)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix694 (2 : Fin 4) = raw4864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix694 raw4864; decide +kernel
    rw [heq]
    exact (canonical4864 hH).trans (sound191 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix694 (3 : Fin 4)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix694 (3 : Fin 4) = raw4863 := by apply Matrix.ext; unfold mergeFirst pivotMatrix694 raw4863; decide +kernel
    rw [heq]
    exact (canonical4863 hH).trans (sound132 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node694 + (injectiveMoment H (mergeFirst pivotMatrix694 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix694 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix694 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix694 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value694, value132, value191, value221, value243, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation695 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix695 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 3, -4]]

theorem sound695 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node695 = Sparse.eval value695 (momentVector H) := by
  have heq : pivotMatrix695 = (fun u v => node695 (pivotPermutation695 u) v) := by apply Matrix.ext; unfold pivotMatrix695 node695 pivotPermutation695; decide +kernel
  have hmoment : injectiveMoment H node695 = injectiveMoment H pivotMatrix695 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix695 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix695 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix695 (0 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix695 (0 : Fin 4) = raw7376 := by apply Matrix.ext; unfold mergeFirst pivotMatrix695 raw7376; decide +kernel
    rw [heq]
    exact (canonical7376 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix695 (1 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix695 (1 : Fin 4) = raw4921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix695 raw4921; decide +kernel
    rw [heq]
    exact (canonical4921 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix695 (2 : Fin 4)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix695 (2 : Fin 4) = raw4879 := by apply Matrix.ext; unfold mergeFirst pivotMatrix695 raw4879; decide +kernel
    rw [heq]
    exact (canonical4879 hH).trans (sound161 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix695 (3 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix695 (3 : Fin 4) = raw4874 := by apply Matrix.ext; unfold mergeFirst pivotMatrix695 raw4874; decide +kernel
    rw [heq]
    exact (canonical4874 hH).trans (sound134 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node695 + (injectiveMoment H (mergeFirst pivotMatrix695 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix695 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix695 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix695 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value695, value134, value161, value225, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation696 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix696 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 2, -3]]

theorem sound696 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node696 = Sparse.eval value696 (momentVector H) := by
  have heq : pivotMatrix696 = (fun u v => node696 (pivotPermutation696 u) v) := by apply Matrix.ext; unfold pivotMatrix696 node696 pivotPermutation696; decide +kernel
  have hmoment : injectiveMoment H node696 = injectiveMoment H pivotMatrix696 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix696 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix696 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix696 (0 : Fin 4)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix696 (0 : Fin 4) = raw5381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix696 raw5381; decide +kernel
    rw [heq]
    exact (canonical5381 hH).trans (sound214 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix696 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix696 (1 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix696 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix696 (2 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix696 (2 : Fin 4) = raw4905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix696 raw4905; decide +kernel
    rw [heq]
    exact (canonical4905 hH).trans (sound222 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix696 (3 : Fin 4)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix696 (3 : Fin 4) = raw4904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix696 raw4904; decide +kernel
    rw [heq]
    exact (canonical4904 hH).trans (sound221 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node696 + (injectiveMoment H (mergeFirst pivotMatrix696 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix696 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix696 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix696 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value696, value214, value221, value222, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation697 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix697 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 1, -2]]

theorem sound697 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node697 = Sparse.eval value697 (momentVector H) := by
  have heq : pivotMatrix697 = (fun u v => node697 (pivotPermutation697 u) v) := by apply Matrix.ext; unfold pivotMatrix697 node697 pivotPermutation697; decide +kernel
  have hmoment : injectiveMoment H node697 = injectiveMoment H pivotMatrix697 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix697 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix697 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix697 (0 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix697 (0 : Fin 4) = raw5382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix697 raw5382; decide +kernel
    rw [heq]
    exact (canonical5382 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix697 (1 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix697 (1 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix697 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix697 (2 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix697 (2 : Fin 4) = raw4906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix697 raw4906; decide +kernel
    rw [heq]
    exact (canonical4906 hH).trans (sound223 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix697 (3 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix697 (3 : Fin 4) = raw4905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix697 raw4905; decide +kernel
    rw [heq]
    exact (canonical4905 hH).trans (sound222 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node697 + (injectiveMoment H (mergeFirst pivotMatrix697 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix697 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix697 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix697 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value697, value210, value215, value222, value223, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation698 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix698 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2]]

theorem sound698 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node698 = Sparse.eval value698 (momentVector H) := by
  have heq : pivotMatrix698 = (fun u v => node698 (pivotPermutation698 u) v) := by apply Matrix.ext; unfold pivotMatrix698 node698 pivotPermutation698; decide +kernel
  have hmoment : injectiveMoment H node698 = injectiveMoment H pivotMatrix698 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix698 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix698 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix698 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix698 (0 : Fin 4) = raw7404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix698 raw7404; decide +kernel
    rw [heq]
    exact (canonical7404 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix698 (1 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix698 (1 : Fin 4) = raw4961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix698 raw4961; decide +kernel
    rw [heq]
    exact (canonical4961 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix698 (2 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix698 (2 : Fin 4) = raw4906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix698 raw4906; decide +kernel
    rw [heq]
    exact (canonical4906 hH).trans (sound223 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix698 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix698 (3 : Fin 4) = raw4901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix698 raw4901; decide +kernel
    rw [heq]
    exact (canonical4901 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node698 + (injectiveMoment H (mergeFirst pivotMatrix698 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix698 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix698 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix698 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value698, value198, value223, value225, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation699 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix699 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 1, 1], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1]]

theorem sound699 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node699 = Sparse.eval value699 (momentVector H) := by
  have heq : pivotMatrix699 = (fun u v => node699 (pivotPermutation699 u) v) := by apply Matrix.ext; unfold pivotMatrix699 node699 pivotPermutation699; decide +kernel
  have hmoment : injectiveMoment H node699 = injectiveMoment H pivotMatrix699 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix699 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix699 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix699 (0 : Fin 4)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix699 (0 : Fin 4) = raw7880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix699 raw7880; decide +kernel
    rw [heq]
    exact (canonical7880 hH).trans (sound292 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix699 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix699 (1 : Fin 4) = raw4964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix699 raw4964; decide +kernel
    rw [heq]
    exact (canonical4964 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix699 (2 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix699 (2 : Fin 4) = raw4907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix699 raw4907; decide +kernel
    rw [heq]
    exact (canonical4907 hH).trans (sound222 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix699 (3 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix699 (3 : Fin 4) = raw4901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix699 raw4901; decide +kernel
    rw [heq]
    exact (canonical4901 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node699 + (injectiveMoment H (mergeFirst pivotMatrix699 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix699 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix699 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix699 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value699, value198, value222, value226, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation700 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix700 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem sound700 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node700 = Sparse.eval value700 (momentVector H) := by
  have heq : pivotMatrix700 = (fun u v => node700 (pivotPermutation700 u) v) := by apply Matrix.ext; unfold pivotMatrix700 node700 pivotPermutation700; decide +kernel
  have hmoment : injectiveMoment H node700 = injectiveMoment H pivotMatrix700 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix700 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix700 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix700 (0 : Fin 4)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix700 (0 : Fin 4) = raw7406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix700 raw7406; decide +kernel
    rw [heq]
    exact (canonical7406 hH).trans (sound289 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix700 (1 : Fin 4)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix700 (1 : Fin 4) = raw4962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix700 raw4962; decide +kernel
    rw [heq]
    exact (canonical4962 hH).trans (sound221 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix700 (2 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix700 (2 : Fin 4) = raw4907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix700 raw4907; decide +kernel
    rw [heq]
    exact (canonical4907 hH).trans (sound222 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix700 (3 : Fin 4)) =
      Sparse.eval value220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix700 (3 : Fin 4) = raw4903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix700 raw4903; decide +kernel
    rw [heq]
    exact (canonical4903 hH).trans (sound220 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node700 + (injectiveMoment H (mergeFirst pivotMatrix700 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix700 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix700 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix700 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value700, value220, value221, value222, value289, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation701 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix701 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem sound701 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node701 = Sparse.eval value701 (momentVector H) := by
  have heq : pivotMatrix701 = (fun u v => node701 (pivotPermutation701 u) v) := by apply Matrix.ext; unfold pivotMatrix701 node701 pivotPermutation701; decide +kernel
  have hmoment : injectiveMoment H node701 = injectiveMoment H pivotMatrix701 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix701 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix701 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix701 (0 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix701 (0 : Fin 4) = raw4042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix701 raw4042; decide +kernel
    rw [heq]
    exact (canonical4042 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix701 (1 : Fin 4)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix701 (1 : Fin 4) = raw4904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix701 raw4904; decide +kernel
    rw [heq]
    exact (canonical4904 hH).trans (sound221 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix701 (2 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix701 (2 : Fin 4) = raw4921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix701 raw4921; decide +kernel
    rw [heq]
    exact (canonical4921 hH).trans (sound225 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix701 (3 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix701 (3 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix701 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node701 + (injectiveMoment H (mergeFirst pivotMatrix701 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix701 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix701 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix701 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value701, value201, value221, value225, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation702 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix702 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 2, -3]]

theorem sound702 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node702 = Sparse.eval value702 (momentVector H) := by
  have heq : pivotMatrix702 = (fun u v => node702 (pivotPermutation702 u) v) := by apply Matrix.ext; unfold pivotMatrix702 node702 pivotPermutation702; decide +kernel
  have hmoment : injectiveMoment H node702 = injectiveMoment H pivotMatrix702 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix702 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix702 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix702 (0 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix702 (0 : Fin 4) = raw4043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix702 raw4043; decide +kernel
    rw [heq]
    exact (canonical4043 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix702 (1 : Fin 4)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix702 (1 : Fin 4) = raw4905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix702 raw4905; decide +kernel
    rw [heq]
    exact (canonical4905 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix702 (2 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix702 (2 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix702 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix702 (3 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix702 (3 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix702 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node702 + (injectiveMoment H (mergeFirst pivotMatrix702 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix702 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix702 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix702 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value702, value169, value210, value222, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation703 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix703 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem sound703 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node703 = Sparse.eval value703 (momentVector H) := by
  have heq : pivotMatrix703 = (fun u v => node703 (pivotPermutation703 u) v) := by apply Matrix.ext; unfold pivotMatrix703 node703 pivotPermutation703; decide +kernel
  have hmoment : injectiveMoment H node703 = injectiveMoment H pivotMatrix703 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix703 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix703 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix703 (0 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix703 (0 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix703 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix703 (1 : Fin 4)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix703 (1 : Fin 4) = raw4906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix703 raw4906; decide +kernel
    rw [heq]
    exact (canonical4906 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix703 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix703 (2 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix703 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix703 (3 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix703 (3 : Fin 4) = raw4924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix703 raw4924; decide +kernel
    rw [heq]
    exact (canonical4924 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node703 + (injectiveMoment H (mergeFirst pivotMatrix703 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix703 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix703 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix703 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value703, value202, value210, value223, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
