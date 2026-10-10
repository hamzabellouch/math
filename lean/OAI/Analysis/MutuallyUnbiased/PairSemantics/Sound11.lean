import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation704 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix704 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]

theorem sound704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node704 = Sparse.eval value704 (momentVector H) := by
  have heq : pivotMatrix704 = (fun u v => node704 (pivotPermutation704 u) v) := by apply Matrix.ext; unfold pivotMatrix704 node704 pivotPermutation704; decide +kernel
  have hmoment : injectiveMoment H node704 = injectiveMoment H pivotMatrix704 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix704 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix704 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix704 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (0 : Fin 4) = raw5384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw5384; decide +kernel
    rw [heq]
    exact (canonical5384 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix704 (1 : Fin 4)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (1 : Fin 4) = raw4943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4943; decide +kernel
    rw [heq]
    exact (canonical4943 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix704 (2 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (2 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix704 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix704 (3 : Fin 4) = raw4915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix704 raw4915; decide +kernel
    rw [heq]
    exact (canonical4915 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node704 + (injectiveMoment H (mergeFirst pivotMatrix704 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix704 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value704, value203, value224, value227, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation705 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix705 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]

theorem sound705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node705 = Sparse.eval value705 (momentVector H) := by
  have heq : pivotMatrix705 = (fun u v => node705 (pivotPermutation705 u) v) := by apply Matrix.ext; unfold pivotMatrix705 node705 pivotPermutation705; decide +kernel
  have hmoment : injectiveMoment H node705 = injectiveMoment H pivotMatrix705 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix705 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix705 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix705 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (0 : Fin 4) = raw5385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw5385; decide +kernel
    rw [heq]
    exact (canonical5385 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix705 (1 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (1 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix705 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (2 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix705 (3 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (3 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node705 + (injectiveMoment H (mergeFirst pivotMatrix705 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value705, value203, value210, value226, value230, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation706 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix706 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem sound706 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node706 = Sparse.eval value706 (momentVector H) := by
  have heq : pivotMatrix706 = (fun u v => node706 (pivotPermutation706 u) v) := by apply Matrix.ext; unfold pivotMatrix706 node706 pivotPermutation706; decide +kernel
  have hmoment : injectiveMoment H node706 = injectiveMoment H pivotMatrix706 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix706 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix706 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix706 (0 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix706 (0 : Fin 4) = raw7412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix706 raw7412; decide +kernel
    rw [heq]
    exact (canonical7412 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix706 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix706 (1 : Fin 4) = raw4964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix706 raw4964; decide +kernel
    rw [heq]
    exact (canonical4964 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix706 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix706 (2 : Fin 4) = raw4924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix706 raw4924; decide +kernel
    rw [heq]
    exact (canonical4924 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix706 (3 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix706 (3 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix706 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node706 + (injectiveMoment H (mergeFirst pivotMatrix706 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix706 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix706 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix706 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value706, value210, value224, value226, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation707 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix707 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem sound707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node707 = Sparse.eval value707 (momentVector H) := by
  have heq : pivotMatrix707 = (fun u v => node707 (pivotPermutation707 u) v) := by apply Matrix.ext; unfold pivotMatrix707 node707 pivotPermutation707; decide +kernel
  have hmoment : injectiveMoment H node707 = injectiveMoment H pivotMatrix707 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix707 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix707 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix707 (0 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix707 (0 : Fin 4) = raw4087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix707 raw4087; decide +kernel
    rw [heq]
    exact (canonical4087 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix707 (1 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix707 (1 : Fin 4) = raw4921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix707 raw4921; decide +kernel
    rw [heq]
    exact (canonical4921 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix707 (2 : Fin 4)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix707 (2 : Fin 4) = raw4944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix707 raw4944; decide +kernel
    rw [heq]
    exact (canonical4944 hH).trans (sound228 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix707 (3 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix707 (3 : Fin 4) = raw4945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix707 raw4945; decide +kernel
    rw [heq]
    exact (canonical4945 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node707 + (injectiveMoment H (mergeFirst pivotMatrix707 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix707 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix707 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix707 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value707, value206, value225, value228, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation708 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix708 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem sound708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node708 = Sparse.eval value708 (momentVector H) := by
  have heq : pivotMatrix708 = (fun u v => node708 (pivotPermutation708 u) v) := by apply Matrix.ext; unfold pivotMatrix708 node708 pivotPermutation708; decide +kernel
  have hmoment : injectiveMoment H node708 = injectiveMoment H pivotMatrix708 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix708 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix708 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix708 (0 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (0 : Fin 4) = raw4088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4088; decide +kernel
    rw [heq]
    exact (canonical4088 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix708 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (1 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix708 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (2 : Fin 4) = raw4945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4945; decide +kernel
    rw [heq]
    exact (canonical4945 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix708 (3 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix708 (3 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix708 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node708 + (injectiveMoment H (mergeFirst pivotMatrix708 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix708 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value708, value185, value226, value229, value230, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation709 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix709 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem sound709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node709 = Sparse.eval value709 (momentVector H) := by
  have heq : pivotMatrix709 = (fun u v => node709 (pivotPermutation709 u) v) := by apply Matrix.ext; unfold pivotMatrix709 node709 pivotPermutation709; decide +kernel
  have hmoment : injectiveMoment H node709 = injectiveMoment H pivotMatrix709 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix709 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix709 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix709 (0 : Fin 4)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix709 (0 : Fin 4) = raw4089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix709 raw4089; decide +kernel
    rw [heq]
    exact (canonical4089 hH).trans (sound284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix709 (1 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix709 (1 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix709 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix709 (2 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix709 (2 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix709 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix709 (3 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix709 (3 : Fin 4) = raw4947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix709 raw4947; decide +kernel
    rw [heq]
    exact (canonical4947 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node709 + (injectiveMoment H (mergeFirst pivotMatrix709 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix709 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix709 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix709 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value709, value210, value230, value284, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation710 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix710 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node710 = Sparse.eval value710 (momentVector H) := by
  have heq : pivotMatrix710 = (fun u v => node710 (pivotPermutation710 u) v) := by apply Matrix.ext; unfold pivotMatrix710 node710 pivotPermutation710; decide +kernel
  have hmoment : injectiveMoment H node710 = injectiveMoment H pivotMatrix710 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix710 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix710 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix710 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (0 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix710 (1 : Fin 4)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (1 : Fin 4) = raw4948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4948; decide +kernel
    rw [heq]
    exact (canonical4948 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix710 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (2 : Fin 4) = raw4953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4953; decide +kernel
    rw [heq]
    exact (canonical4953 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix710 (3 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix710 (3 : Fin 4) = raw4954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix710 raw4954; decide +kernel
    rw [heq]
    exact (canonical4954 hH).trans (sound230 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node710 + (injectiveMoment H (mergeFirst pivotMatrix710 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix710 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix710 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix710 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value710, value210, value229, value230, value44, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation711 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix711 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound711 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node711 = Sparse.eval value711 (momentVector H) := by
  have heq : pivotMatrix711 = (fun u v => node711 (pivotPermutation711 u) v) := by apply Matrix.ext; unfold pivotMatrix711 node711 pivotPermutation711; decide +kernel
  have hmoment : injectiveMoment H node711 = injectiveMoment H pivotMatrix711 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix711 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix711 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix711 (0 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (0 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix711 (1 : Fin 4)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (1 : Fin 4) = raw4949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4949; decide +kernel
    rw [heq]
    exact (canonical4949 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix711 (2 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (2 : Fin 4) = raw4954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4954; decide +kernel
    rw [heq]
    exact (canonical4954 hH).trans (sound230 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix711 (3 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (3 : Fin 4) = raw4955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4955; decide +kernel
    rw [heq]
    exact (canonical4955 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node711 + (injectiveMoment H (mergeFirst pivotMatrix711 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix711 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix711 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix711 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value711, value230, value287, value294, value61, Sparse.eval] at hc ⊢
  linarith

theorem sound712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node712 = Sparse.eval value712 (momentVector H) := by
  have hc : momentVector H 798 = injectiveMoment H node712 := rfl
  simp [value712, Sparse.eval, hc]

theorem sound713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node713 = Sparse.eval value713 (momentVector H) := by
  have hc : momentVector H 810 = injectiveMoment H node713 := rfl
  simp [value713, Sparse.eval, hc]

theorem sound714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node714 = Sparse.eval value714 (momentVector H) := by
  have hc : momentVector H 811 = injectiveMoment H node714 := rfl
  simp [value714, Sparse.eval, hc]

def pivotPermutation715 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix715 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

theorem sound715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node715 = Sparse.eval value715 (momentVector H) := by
  have heq : pivotMatrix715 = (fun u v => node715 (pivotPermutation715 u) v) := by apply Matrix.ext; unfold pivotMatrix715 node715 pivotPermutation715; decide +kernel
  have hmoment : injectiveMoment H node715 = injectiveMoment H pivotMatrix715 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix715 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix715 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix715 (0 : Fin 5)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix715 (0 : Fin 5) = raw849 := by apply Matrix.ext; unfold mergeFirst pivotMatrix715 raw849; decide +kernel
    rw [heq]
    exact (canonical849 hH).trans (sound117 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix715 (1 : Fin 5)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : mergeFirst pivotMatrix715 (1 : Fin 5) = raw5101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix715 raw5101; decide +kernel
    rw [heq]
    exact (canonical5101 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix715 (2 : Fin 5)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix715 (2 : Fin 5) = raw5106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix715 raw5106; decide +kernel
    rw [heq]
    exact (canonical5106 hH).trans (sound45 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix715 (3 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix715 (3 : Fin 5) = raw5110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix715 raw5110; decide +kernel
    rw [heq]
    exact (canonical5110 hH).trans (sound231 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix715 (4 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix715 (4 : Fin 5) = raw5111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix715 raw5111; decide +kernel
    rw [heq]
    exact (canonical5111 hH).trans (sound231 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node715 + (injectiveMoment H (mergeFirst pivotMatrix715 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix715 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix715 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix715 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix715 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value715, value117, value231, value45, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation716 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix716 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

theorem sound716 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node716 = Sparse.eval value716 (momentVector H) := by
  have heq : pivotMatrix716 = (fun u v => node716 (pivotPermutation716 u) v) := by apply Matrix.ext; unfold pivotMatrix716 node716 pivotPermutation716; decide +kernel
  have hmoment : injectiveMoment H node716 = injectiveMoment H pivotMatrix716 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix716 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix716 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix716 (0 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (0 : Fin 5) = raw7634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw7634; decide +kernel
    rw [heq]
    exact (canonical7634 hH).trans (sound232 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix716 (1 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (1 : Fin 5) = raw5139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5139; decide +kernel
    rw [heq]
    exact (canonical5139 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix716 (2 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (2 : Fin 5) = raw5115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5115; decide +kernel
    rw [heq]
    exact (canonical5115 hH).trans (sound231 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix716 (3 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (3 : Fin 5) = raw5111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5111; decide +kernel
    rw [heq]
    exact (canonical5111 hH).trans (sound231 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix716 (4 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix716 (4 : Fin 5) = raw5110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix716 raw5110; decide +kernel
    rw [heq]
    exact (canonical5110 hH).trans (sound231 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node716 + (injectiveMoment H (mergeFirst pivotMatrix716 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix716 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value716, value231, value232, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation717 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix717 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem sound717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node717 = Sparse.eval value717 (momentVector H) := by
  have heq : pivotMatrix717 = (fun u v => node717 (pivotPermutation717 u) v) := by apply Matrix.ext; unfold pivotMatrix717 node717 pivotPermutation717; decide +kernel
  have hmoment : injectiveMoment H node717 = injectiveMoment H pivotMatrix717 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix717 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix717 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix717 (0 : Fin 5)) =
      Sparse.eval value118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (0 : Fin 5) = raw867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw867; decide +kernel
    rw [heq]
    exact (canonical867 hH).trans (sound118 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix717 (1 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (1 : Fin 5) = raw5110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5110; decide +kernel
    rw [heq]
    exact (canonical5110 hH).trans (sound231 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix717 (2 : Fin 5)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (2 : Fin 5) = raw5128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5128; decide +kernel
    rw [heq]
    exact (canonical5128 hH).trans (sound46 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix717 (3 : Fin 5)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (3 : Fin 5) = raw5136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5136; decide +kernel
    rw [heq]
    exact (canonical5136 hH).trans (sound46 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix717 (4 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (4 : Fin 5) = raw5139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5139; decide +kernel
    rw [heq]
    exact (canonical5139 hH).trans (sound232 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node717 + (injectiveMoment H (mergeFirst pivotMatrix717 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value717, value118, value231, value232, value46, Sparse.eval] at hc ⊢
  linarith

theorem sound718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node718 = Sparse.eval value718 (momentVector H) := by
  have hc : momentVector H 812 = injectiveMoment H node718 := rfl
  simp [value718, Sparse.eval, hc]

theorem sound719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node719 = Sparse.eval value719 (momentVector H) := by
  have hc : momentVector H 230 = injectiveMoment H node719 := rfl
  simp [value719, Sparse.eval, hc]

theorem sound720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node720 = Sparse.eval value720 (momentVector H) := by
  have hc : momentVector H 231 = injectiveMoment H node720 := rfl
  simp [value720, Sparse.eval, hc]

def pivotPermutation721 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix721 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound721 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node721 = Sparse.eval value721 (momentVector H) := by
  have heq : pivotMatrix721 = (fun u v => node721 (pivotPermutation721 u) v) := by apply Matrix.ext; unfold pivotMatrix721 node721 pivotPermutation721; decide +kernel
  have hmoment : injectiveMoment H node721 = injectiveMoment H pivotMatrix721 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix721 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix721 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix721 (0 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix721 (0 : Fin 4) = raw5499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix721 raw5499; decide +kernel
    rw [heq]
    exact (canonical5499 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix721 (1 : Fin 4)) =
      Sparse.eval value235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix721 (1 : Fin 4) = raw5466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix721 raw5466; decide +kernel
    rw [heq]
    exact (canonical5466 hH).trans (sound235 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix721 (2 : Fin 4)) =
      Sparse.eval value234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix721 (2 : Fin 4) = raw5463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix721 raw5463; decide +kernel
    rw [heq]
    exact (canonical5463 hH).trans (sound234 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix721 (3 : Fin 4)) =
      Sparse.eval value233 (momentVector H) := by
    have heq : mergeFirst pivotMatrix721 (3 : Fin 4) = raw5462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix721 raw5462; decide +kernel
    rw [heq]
    exact (canonical5462 hH).trans (sound233 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node721 + (injectiveMoment H (mergeFirst pivotMatrix721 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix721 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix721 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix721 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value721, value233, value234, value235, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation722 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix722 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound722 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node722 = Sparse.eval value722 (momentVector H) := by
  have heq : pivotMatrix722 = (fun u v => node722 (pivotPermutation722 u) v) := by apply Matrix.ext; unfold pivotMatrix722 node722 pivotPermutation722; decide +kernel
  have hmoment : injectiveMoment H node722 = injectiveMoment H pivotMatrix722 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix722 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix722 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix722 (0 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix722 (0 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix722 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix722 (1 : Fin 4)) =
      Sparse.eval value236 (momentVector H) := by
    have heq : mergeFirst pivotMatrix722 (1 : Fin 4) = raw5469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix722 raw5469; decide +kernel
    rw [heq]
    exact (canonical5469 hH).trans (sound236 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix722 (2 : Fin 4)) =
      Sparse.eval value235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix722 (2 : Fin 4) = raw5467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix722 raw5467; decide +kernel
    rw [heq]
    exact (canonical5467 hH).trans (sound235 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix722 (3 : Fin 4)) =
      Sparse.eval value235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix722 (3 : Fin 4) = raw5466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix722 raw5466; decide +kernel
    rw [heq]
    exact (canonical5466 hH).trans (sound235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node722 + (injectiveMoment H (mergeFirst pivotMatrix722 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix722 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix722 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix722 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value722, value235, value236, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation723 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix723 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem sound723 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node723 = Sparse.eval value723 (momentVector H) := by
  have heq : pivotMatrix723 = (fun u v => node723 (pivotPermutation723 u) v) := by apply Matrix.ext; unfold pivotMatrix723 node723 pivotPermutation723; decide +kernel
  have hmoment : injectiveMoment H node723 = injectiveMoment H pivotMatrix723 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix723 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix723 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix723 (0 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix723 (0 : Fin 4) = raw5530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix723 raw5530; decide +kernel
    rw [heq]
    exact (canonical5530 hH).trans (sound253 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix723 (1 : Fin 4)) =
      Sparse.eval value238 (momentVector H) := by
    have heq : mergeFirst pivotMatrix723 (1 : Fin 4) = raw5481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix723 raw5481; decide +kernel
    rw [heq]
    exact (canonical5481 hH).trans (sound238 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix723 (2 : Fin 4)) =
      Sparse.eval value238 (momentVector H) := by
    have heq : mergeFirst pivotMatrix723 (2 : Fin 4) = raw5477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix723 raw5477; decide +kernel
    rw [heq]
    exact (canonical5477 hH).trans (sound238 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix723 (3 : Fin 4)) =
      Sparse.eval value237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix723 (3 : Fin 4) = raw5475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix723 raw5475; decide +kernel
    rw [heq]
    exact (canonical5475 hH).trans (sound237 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node723 + (injectiveMoment H (mergeFirst pivotMatrix723 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix723 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix723 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix723 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value723, value237, value238, value253, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation724 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix724 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem sound724 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node724 = Sparse.eval value724 (momentVector H) := by
  have heq : pivotMatrix724 = (fun u v => node724 (pivotPermutation724 u) v) := by apply Matrix.ext; unfold pivotMatrix724 node724 pivotPermutation724; decide +kernel
  have hmoment : injectiveMoment H node724 = injectiveMoment H pivotMatrix724 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix724 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix724 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix724 (0 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix724 (0 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix724 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix724 (1 : Fin 4)) =
      Sparse.eval value240 (momentVector H) := by
    have heq : mergeFirst pivotMatrix724 (1 : Fin 4) = raw5482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix724 raw5482; decide +kernel
    rw [heq]
    exact (canonical5482 hH).trans (sound240 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix724 (2 : Fin 4)) =
      Sparse.eval value239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix724 (2 : Fin 4) = raw5478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix724 raw5478; decide +kernel
    rw [heq]
    exact (canonical5478 hH).trans (sound239 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix724 (3 : Fin 4)) =
      Sparse.eval value238 (momentVector H) := by
    have heq : mergeFirst pivotMatrix724 (3 : Fin 4) = raw5477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix724 raw5477; decide +kernel
    rw [heq]
    exact (canonical5477 hH).trans (sound238 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node724 + (injectiveMoment H (mergeFirst pivotMatrix724 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix724 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix724 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix724 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value724, value238, value239, value240, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation725 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix725 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 1, 2], ![1, 2, -2, -1], ![3, -2, 1, -2]]

theorem sound725 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node725 = Sparse.eval value725 (momentVector H) := by
  have heq : pivotMatrix725 = (fun u v => node725.transpose (pivotPermutation725 u) v) := by apply Matrix.ext; unfold pivotMatrix725 node725 pivotPermutation725; decide +kernel
  have hmoment : injectiveMoment H node725 = injectiveMoment H pivotMatrix725 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix725 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix725 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix725 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix725 (0 : Fin 3) = raw54 := by apply Matrix.ext; unfold mergeFirst pivotMatrix725 raw54; decide +kernel
    rw [heq]
    exact (canonical54 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix725 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix725 (1 : Fin 3) = raw346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix725 raw346; decide +kernel
    rw [heq]
    exact (canonical346 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix725 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix725 (2 : Fin 3) = raw353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix725 raw353; decide +kernel
    rw [heq]
    exact (canonical353 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node725 + (injectiveMoment H (mergeFirst pivotMatrix725 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix725 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix725 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value725, value111, value191, value198, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation726 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix726 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 2, 1], ![1, 2, -2, -1], ![3, -2, 0, -1]]

theorem sound726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node726 = Sparse.eval value726 (momentVector H) := by
  have heq : pivotMatrix726 = (fun u v => node726.transpose (pivotPermutation726 u) v) := by apply Matrix.ext; unfold pivotMatrix726 node726 pivotPermutation726; decide +kernel
  have hmoment : injectiveMoment H node726 = injectiveMoment H pivotMatrix726 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix726 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix726 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix726 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix726 (0 : Fin 3) = raw56 := by apply Matrix.ext; unfold mergeFirst pivotMatrix726 raw56; decide +kernel
    rw [heq]
    exact (canonical56 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix726 (1 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix726 (1 : Fin 3) = raw361 := by apply Matrix.ext; unfold mergeFirst pivotMatrix726 raw361; decide +kernel
    rw [heq]
    exact (canonical361 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix726 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix726 (2 : Fin 3) = raw366 := by apply Matrix.ext; unfold mergeFirst pivotMatrix726 raw366; decide +kernel
    rw [heq]
    exact (canonical366 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node726 + (injectiveMoment H (mergeFirst pivotMatrix726 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix726 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix726 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value726, value177, value204, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation727 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix727 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 3, 0], ![1, 2, -1, -2], ![3, -2, -2, 1]]

theorem sound727 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node727 = Sparse.eval value727 (momentVector H) := by
  have heq : pivotMatrix727 = (fun u v => node727.transpose (pivotPermutation727 u) v) := by apply Matrix.ext; unfold pivotMatrix727 node727 pivotPermutation727; decide +kernel
  have hmoment : injectiveMoment H node727 = injectiveMoment H pivotMatrix727 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix727 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix727 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix727 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix727 (0 : Fin 3) = raw57 := by apply Matrix.ext; unfold mergeFirst pivotMatrix727 raw57; decide +kernel
    rw [heq]
    exact (canonical57 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix727 (1 : Fin 3)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix727 (1 : Fin 3) = raw585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix727 raw585; decide +kernel
    rw [heq]
    exact (canonical585 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix727 (2 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix727 (2 : Fin 3) = raw587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix727 raw587; decide +kernel
    rw [heq]
    exact (canonical587 hH).trans (sound101 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node727 + (injectiveMoment H (mergeFirst pivotMatrix727 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix727 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix727 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value727, value101, value191, value214, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation728 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix728 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 1, 2], ![2, -2, 1, -1], ![2, 2, -2, -2]]

theorem sound728 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node728 = Sparse.eval value728 (momentVector H) := by
  have heq : pivotMatrix728 = (fun u v => node728.transpose (pivotPermutation728 u) v) := by apply Matrix.ext; unfold pivotMatrix728 node728 pivotPermutation728; decide +kernel
  have hmoment : injectiveMoment H node728 = injectiveMoment H pivotMatrix728 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix728 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix728 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix728 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix728 (0 : Fin 3) = raw55 := by apply Matrix.ext; unfold mergeFirst pivotMatrix728 raw55; decide +kernel
    rw [heq]
    exact (canonical55 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix728 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix728 (1 : Fin 3) = raw349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix728 raw349; decide +kernel
    rw [heq]
    exact (canonical349 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix728 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix728 (2 : Fin 3) = raw354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix728 raw354; decide +kernel
    rw [heq]
    exact (canonical354 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node728 + (injectiveMoment H (mergeFirst pivotMatrix728 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix728 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix728 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value728, value111, value135, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation729 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix729 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 0, 3, 0], ![2, -2, -1, 1], ![2, 2, -2, -2]]

theorem sound729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node729 = Sparse.eval value729 (momentVector H) := by
  have heq : pivotMatrix729 = (fun u v => node729.transpose (pivotPermutation729 u) v) := by apply Matrix.ext; unfold pivotMatrix729 node729 pivotPermutation729; decide +kernel
  have hmoment : injectiveMoment H node729 = injectiveMoment H pivotMatrix729 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix729 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix729 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix729 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix729 (0 : Fin 3) = raw58 := by apply Matrix.ext; unfold mergeFirst pivotMatrix729 raw58; decide +kernel
    rw [heq]
    exact (canonical58 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix729 (1 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix729 (1 : Fin 3) = raw586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix729 raw586; decide +kernel
    rw [heq]
    exact (canonical586 hH).trans (sound101 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix729 (2 : Fin 3)) =
      Sparse.eval value105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix729 (2 : Fin 3) = raw588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix729 raw588; decide +kernel
    rw [heq]
    exact (canonical588 hH).trans (sound105 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node729 + (injectiveMoment H (mergeFirst pivotMatrix729 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix729 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix729 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value729, value101, value105, value135, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation730 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix730 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 1, 1, 1], ![2, -2, 1, -1], ![2, 1, -2, -1]]

theorem sound730 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node730 = Sparse.eval value730 (momentVector H) := by
  have heq : pivotMatrix730 = (fun u v => node730.transpose (pivotPermutation730 u) v) := by apply Matrix.ext; unfold pivotMatrix730 node730 pivotPermutation730; decide +kernel
  have hmoment : injectiveMoment H node730 = injectiveMoment H pivotMatrix730 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix730 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix730 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix730 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix730 (0 : Fin 3) = raw74 := by apply Matrix.ext; unfold mergeFirst pivotMatrix730 raw74; decide +kernel
    rw [heq]
    exact (canonical74 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix730 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix730 (1 : Fin 3) = raw594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix730 raw594; decide +kernel
    rw [heq]
    exact (canonical594 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix730 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix730 (2 : Fin 3) = raw596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix730 raw596; decide +kernel
    rw [heq]
    exact (canonical596 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node730 + (injectiveMoment H (mergeFirst pivotMatrix730 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix730 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix730 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value730, value134, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation731 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-3, 1, 2, 0], ![2, -2, -1, 1], ![2, 1, -1, -2]]

theorem sound731 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node731 = Sparse.eval value731 (momentVector H) := by
  have heq : pivotMatrix731 = (fun u v => node731.transpose (pivotPermutation731 u) v) := by apply Matrix.ext; unfold pivotMatrix731 node731 pivotPermutation731; decide +kernel
  have hmoment : injectiveMoment H node731 = injectiveMoment H pivotMatrix731 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix731 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix731 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix731 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix731 (0 : Fin 3) = raw75 := by apply Matrix.ext; unfold mergeFirst pivotMatrix731 raw75; decide +kernel
    rw [heq]
    exact (canonical75 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix731 (1 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix731 (1 : Fin 3) = raw817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix731 raw817; decide +kernel
    rw [heq]
    exact (canonical817 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix731 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix731 (2 : Fin 3) = raw821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix731 raw821; decide +kernel
    rw [heq]
    exact (canonical821 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node731 + (injectiveMoment H (mergeFirst pivotMatrix731 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix731 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix731 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value731, value111, value134, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation732 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem sound732 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node732 = Sparse.eval value732 (momentVector H) := by
  have heq : pivotMatrix732 = (fun u v => node732 (pivotPermutation732 u) v) := by apply Matrix.ext; unfold pivotMatrix732 node732 pivotPermutation732; decide +kernel
  have hmoment : injectiveMoment H node732 = injectiveMoment H pivotMatrix732 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix732 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix732 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix732 (0 : Fin 4)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix732 (0 : Fin 4) = raw944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix732 raw944; decide +kernel
    rw [heq]
    exact (canonical944 hH).trans (sound123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix732 (1 : Fin 4)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix732 (1 : Fin 4) = raw5492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix732 raw5492; decide +kernel
    rw [heq]
    exact (canonical5492 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix732 (2 : Fin 4)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix732 (2 : Fin 4) = raw5524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix732 raw5524; decide +kernel
    rw [heq]
    exact (canonical5524 hH).trans (sound51 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix732 (3 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix732 (3 : Fin 4) = raw5538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix732 raw5538; decide +kernel
    rw [heq]
    exact (canonical5538 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node732 + (injectiveMoment H (mergeFirst pivotMatrix732 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix732 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix732 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix732 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value732, value123, value243, value254, value51, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation733 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem sound733 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node733 = Sparse.eval value733 (momentVector H) := by
  have heq : pivotMatrix733 = (fun u v => node733 (pivotPermutation733 u) v) := by apply Matrix.ext; unfold pivotMatrix733 node733 pivotPermutation733; decide +kernel
  have hmoment : injectiveMoment H node733 = injectiveMoment H pivotMatrix733 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix733 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix733 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix733 (0 : Fin 4)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix733 (0 : Fin 4) = raw945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix733 raw945; decide +kernel
    rw [heq]
    exact (canonical945 hH).trans (sound124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix733 (1 : Fin 4)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix733 (1 : Fin 4) = raw5493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix733 raw5493; decide +kernel
    rw [heq]
    exact (canonical5493 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix733 (2 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix733 (2 : Fin 4) = raw5530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix733 raw5530; decide +kernel
    rw [heq]
    exact (canonical5530 hH).trans (sound253 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix733 (3 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix733 (3 : Fin 4) = raw5539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix733 raw5539; decide +kernel
    rw [heq]
    exact (canonical5539 hH).trans (sound253 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node733 + (injectiveMoment H (mergeFirst pivotMatrix733 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix733 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix733 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix733 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value733, value124, value244, value253, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation734 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node734 = Sparse.eval value734 (momentVector H) := by
  have heq : pivotMatrix734 = (fun u v => node734 (pivotPermutation734 u) v) := by apply Matrix.ext; unfold pivotMatrix734 node734 pivotPermutation734; decide +kernel
  have hmoment : injectiveMoment H node734 = injectiveMoment H pivotMatrix734 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix734 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix734 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix734 (0 : Fin 4)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix734 (0 : Fin 4) = raw957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix734 raw957; decide +kernel
    rw [heq]
    exact (canonical957 hH).trans (sound129 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix734 (1 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix734 (1 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix734 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix734 (2 : Fin 4)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix734 (2 : Fin 4) = raw5548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix734 raw5548; decide +kernel
    rw [heq]
    exact (canonical5548 hH).trans (sound53 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix734 (3 : Fin 4)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix734 (3 : Fin 4) = raw5551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix734 raw5551; decide +kernel
    rw [heq]
    exact (canonical5551 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node734 + (injectiveMoment H (mergeFirst pivotMatrix734 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix734 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix734 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix734 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value734, value129, value248, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation735 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix735 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem sound735 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node735 = Sparse.eval value735 (momentVector H) := by
  have heq : pivotMatrix735 = (fun u v => node735 (pivotPermutation735 u) v) := by apply Matrix.ext; unfold pivotMatrix735 node735 pivotPermutation735; decide +kernel
  have hmoment : injectiveMoment H node735 = injectiveMoment H pivotMatrix735 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix735 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix735 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix735 (0 : Fin 4)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix735 (0 : Fin 4) = raw1378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix735 raw1378; decide +kernel
    rw [heq]
    exact (canonical1378 hH).trans (sound144 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix735 (1 : Fin 4)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix735 (1 : Fin 4) = raw5489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix735 raw5489; decide +kernel
    rw [heq]
    exact (canonical5489 hH).trans (sound241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix735 (2 : Fin 4)) =
      Sparse.eval value250 (momentVector H) := by
    have heq : mergeFirst pivotMatrix735 (2 : Fin 4) = raw5514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix735 raw5514; decide +kernel
    rw [heq]
    exact (canonical5514 hH).trans (sound250 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix735 (3 : Fin 4)) =
      Sparse.eval value251 (momentVector H) := by
    have heq : mergeFirst pivotMatrix735 (3 : Fin 4) = raw5516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix735 raw5516; decide +kernel
    rw [heq]
    exact (canonical5516 hH).trans (sound251 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node735 + (injectiveMoment H (mergeFirst pivotMatrix735 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix735 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix735 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix735 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value735, value144, value241, value250, value251, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation736 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node736 = Sparse.eval value736 (momentVector H) := by
  have heq : pivotMatrix736 = (fun u v => node736 (pivotPermutation736 u) v) := by apply Matrix.ext; unfold pivotMatrix736 node736 pivotPermutation736; decide +kernel
  have hmoment : injectiveMoment H node736 = injectiveMoment H pivotMatrix736 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix736 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix736 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix736 (0 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix736 (0 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix736 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix736 (1 : Fin 4)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix736 (1 : Fin 4) = raw5498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix736 raw5498; decide +kernel
    rw [heq]
    exact (canonical5498 hH).trans (sound245 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix736 (2 : Fin 4)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix736 (2 : Fin 4) = raw5524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix736 raw5524; decide +kernel
    rw [heq]
    exact (canonical5524 hH).trans (sound51 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix736 (3 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix736 (3 : Fin 4) = raw5537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix736 raw5537; decide +kernel
    rw [heq]
    exact (canonical5537 hH).trans (sound255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node736 + (injectiveMoment H (mergeFirst pivotMatrix736 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix736 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix736 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix736 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value736, value149, value245, value255, value51, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation737 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node737 = Sparse.eval value737 (momentVector H) := by
  have heq : pivotMatrix737 = (fun u v => node737 (pivotPermutation737 u) v) := by apply Matrix.ext; unfold pivotMatrix737 node737 pivotPermutation737; decide +kernel
  have hmoment : injectiveMoment H node737 = injectiveMoment H pivotMatrix737 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix737 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix737 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix737 (0 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix737 (0 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix737 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix737 (1 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix737 (1 : Fin 4) = raw5499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix737 raw5499; decide +kernel
    rw [heq]
    exact (canonical5499 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix737 (2 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix737 (2 : Fin 4) = raw5530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix737 raw5530; decide +kernel
    rw [heq]
    exact (canonical5530 hH).trans (sound253 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix737 (3 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix737 (3 : Fin 4) = raw5538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix737 raw5538; decide +kernel
    rw [heq]
    exact (canonical5538 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node737 + (injectiveMoment H (mergeFirst pivotMatrix737 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix737 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix737 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix737 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value737, value150, value246, value253, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation738 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound738 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node738 = Sparse.eval value738 (momentVector H) := by
  have heq : pivotMatrix738 = (fun u v => node738 (pivotPermutation738 u) v) := by apply Matrix.ext; unfold pivotMatrix738 node738 pivotPermutation738; decide +kernel
  have hmoment : injectiveMoment H node738 = injectiveMoment H pivotMatrix738 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix738 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix738 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix738 (0 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix738 (0 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix738 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix738 (1 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix738 (1 : Fin 4) = raw5505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix738 raw5505; decide +kernel
    rw [heq]
    exact (canonical5505 hH).trans (sound247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix738 (2 : Fin 4)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix738 (2 : Fin 4) = raw5541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix738 raw5541; decide +kernel
    rw [heq]
    exact (canonical5541 hH).trans (sound52 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix738 (3 : Fin 4)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix738 (3 : Fin 4) = raw5545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix738 raw5545; decide +kernel
    rw [heq]
    exact (canonical5545 hH).trans (sound256 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node738 + (injectiveMoment H (mergeFirst pivotMatrix738 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix738 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix738 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix738 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value738, value153, value247, value256, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation739 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node739 = Sparse.eval value739 (momentVector H) := by
  have heq : pivotMatrix739 = (fun u v => node739 (pivotPermutation739 u) v) := by apply Matrix.ext; unfold pivotMatrix739 node739 pivotPermutation739; decide +kernel
  have hmoment : injectiveMoment H node739 = injectiveMoment H pivotMatrix739 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix739 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix739 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix739 (0 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix739 (0 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix739 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix739 (1 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix739 (1 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix739 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix739 (2 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix739 (2 : Fin 4) = raw5543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix739 raw5543; decide +kernel
    rw [heq]
    exact (canonical5543 hH).trans (sound254 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix739 (3 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix739 (3 : Fin 4) = raw5546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix739 raw5546; decide +kernel
    rw [heq]
    exact (canonical5546 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node739 + (injectiveMoment H (mergeFirst pivotMatrix739 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix739 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix739 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix739 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value739, value145, value248, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation740 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound740 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node740 = Sparse.eval value740 (momentVector H) := by
  have heq : pivotMatrix740 = (fun u v => node740 (pivotPermutation740 u) v) := by apply Matrix.ext; unfold pivotMatrix740 node740 pivotPermutation740; decide +kernel
  have hmoment : injectiveMoment H node740 = injectiveMoment H pivotMatrix740 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix740 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix740 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix740 (0 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix740 (0 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix740 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix740 (1 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix740 (1 : Fin 4) = raw5509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix740 raw5509; decide +kernel
    rw [heq]
    exact (canonical5509 hH).trans (sound249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix740 (2 : Fin 4)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix740 (2 : Fin 4) = raw5548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix740 raw5548; decide +kernel
    rw [heq]
    exact (canonical5548 hH).trans (sound53 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix740 (3 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix740 (3 : Fin 4) = raw5549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix740 raw5549; decide +kernel
    rw [heq]
    exact (canonical5549 hH).trans (sound255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node740 + (injectiveMoment H (mergeFirst pivotMatrix740 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix740 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix740 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix740 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value740, value155, value249, value255, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation741 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix741 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node741 = Sparse.eval value741 (momentVector H) := by
  have heq : pivotMatrix741 = (fun u v => node741 (pivotPermutation741 u) v) := by apply Matrix.ext; unfold pivotMatrix741 node741 pivotPermutation741; decide +kernel
  have hmoment : injectiveMoment H node741 = injectiveMoment H pivotMatrix741 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix741 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix741 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix741 (0 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix741 (0 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix741 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix741 (1 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix741 (1 : Fin 4) = raw5505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix741 raw5505; decide +kernel
    rw [heq]
    exact (canonical5505 hH).trans (sound247 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix741 (2 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix741 (2 : Fin 4) = raw5499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix741 raw5499; decide +kernel
    rw [heq]
    exact (canonical5499 hH).trans (sound246 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix741 (3 : Fin 4)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix741 (3 : Fin 4) = raw5498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix741 raw5498; decide +kernel
    rw [heq]
    exact (canonical5498 hH).trans (sound245 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node741 + (injectiveMoment H (mergeFirst pivotMatrix741 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix741 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix741 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix741 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value741, value245, value246, value247, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation742 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix742 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node742 = Sparse.eval value742 (momentVector H) := by
  have heq : pivotMatrix742 = (fun u v => node742 (pivotPermutation742 u) v) := by apply Matrix.ext; unfold pivotMatrix742 node742 pivotPermutation742; decide +kernel
  have hmoment : injectiveMoment H node742 = injectiveMoment H pivotMatrix742 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix742 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix742 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix742 (0 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix742 (0 : Fin 4) = raw5889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix742 raw5889; decide +kernel
    rw [heq]
    exact (canonical5889 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix742 (1 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix742 (1 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix742 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix742 (2 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix742 (2 : Fin 4) = raw5500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix742 raw5500; decide +kernel
    rw [heq]
    exact (canonical5500 hH).trans (sound246 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix742 (3 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix742 (3 : Fin 4) = raw5499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix742 raw5499; decide +kernel
    rw [heq]
    exact (canonical5499 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node742 + (injectiveMoment H (mergeFirst pivotMatrix742 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix742 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix742 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix742 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value742, value176, value246, value248, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation743 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix743 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1]]

theorem sound743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node743 = Sparse.eval value743 (momentVector H) := by
  have heq : pivotMatrix743 = (fun u v => node743 (pivotPermutation743 u) v) := by apply Matrix.ext; unfold pivotMatrix743 node743 pivotPermutation743; decide +kernel
  have hmoment : injectiveMoment H node743 = injectiveMoment H pivotMatrix743 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix743 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix743 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix743 (0 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (0 : Fin 4) = raw7983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw7983; decide +kernel
    rw [heq]
    exact (canonical7983 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix743 (1 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (1 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix743 (2 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (2 : Fin 4) = raw5500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw5500; decide +kernel
    rw [heq]
    exact (canonical5500 hH).trans (sound246 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix743 (3 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (3 : Fin 4) = raw5497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw5497; decide +kernel
    rw [heq]
    exact (canonical5497 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node743 + (injectiveMoment H (mergeFirst pivotMatrix743 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix743 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix743 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix743 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value743, value225, value246, value254, value281, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation744 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix744 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node744 = Sparse.eval value744 (momentVector H) := by
  have heq : pivotMatrix744 = (fun u v => node744 (pivotPermutation744 u) v) := by apply Matrix.ext; unfold pivotMatrix744 node744 pivotPermutation744; decide +kernel
  have hmoment : injectiveMoment H node744 = injectiveMoment H pivotMatrix744 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix744 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix744 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix744 (0 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (0 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix744 (1 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (1 : Fin 4) = raw5509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5509; decide +kernel
    rw [heq]
    exact (canonical5509 hH).trans (sound249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix744 (2 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (2 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix744 (3 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (3 : Fin 4) = raw5505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5505; decide +kernel
    rw [heq]
    exact (canonical5505 hH).trans (sound247 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node744 + (injectiveMoment H (mergeFirst pivotMatrix744 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix744 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix744 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix744 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value744, value247, value248, value249, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation745 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix745 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![-1, 4, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node745 = Sparse.eval value745 (momentVector H) := by
  have heq : pivotMatrix745 = (fun u v => node745 (pivotPermutation745 u) v) := by apply Matrix.ext; unfold pivotMatrix745 node745 pivotPermutation745; decide +kernel
  have hmoment : injectiveMoment H node745 = injectiveMoment H pivotMatrix745 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix745 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix745 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix745 (0 : Fin 4)) =
      Sparse.eval value236 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (0 : Fin 4) = raw5469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5469; decide +kernel
    rw [heq]
    exact (canonical5469 hH).trans (sound236 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix745 (1 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (1 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix745 (2 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (2 : Fin 4) = raw5509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5509; decide +kernel
    rw [heq]
    exact (canonical5509 hH).trans (sound249 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix745 (3 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (3 : Fin 4) = raw5510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5510; decide +kernel
    rw [heq]
    exact (canonical5510 hH).trans (sound249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node745 + (injectiveMoment H (mergeFirst pivotMatrix745 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix745 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix745 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix745 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value745, value236, value248, value249, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation746 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix746 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

theorem sound746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node746 = Sparse.eval value746 (momentVector H) := by
  have heq : pivotMatrix746 = (fun u v => node746 (pivotPermutation746 u) v) := by apply Matrix.ext; unfold pivotMatrix746 node746 pivotPermutation746; decide +kernel
  have hmoment : injectiveMoment H node746 = injectiveMoment H pivotMatrix746 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix746 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix746 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix746 (0 : Fin 4)) =
      Sparse.eval value237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix746 (0 : Fin 4) = raw5475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix746 raw5475; decide +kernel
    rw [heq]
    exact (canonical5475 hH).trans (sound237 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix746 (1 : Fin 4)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix746 (1 : Fin 4) = raw5517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix746 raw5517; decide +kernel
    rw [heq]
    exact (canonical5517 hH).trans (sound51 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix746 (2 : Fin 4)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix746 (2 : Fin 4) = raw5524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix746 raw5524; decide +kernel
    rw [heq]
    exact (canonical5524 hH).trans (sound51 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix746 (3 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix746 (3 : Fin 4) = raw5530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix746 raw5530; decide +kernel
    rw [heq]
    exact (canonical5530 hH).trans (sound253 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node746 + (injectiveMoment H (mergeFirst pivotMatrix746 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix746 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix746 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix746 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value746, value237, value253, value51, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation747 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix747 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

theorem sound747 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node747 = Sparse.eval value747 (momentVector H) := by
  have heq : pivotMatrix747 = (fun u v => node747 (pivotPermutation747 u) v) := by apply Matrix.ext; unfold pivotMatrix747 node747 pivotPermutation747; decide +kernel
  have hmoment : injectiveMoment H node747 = injectiveMoment H pivotMatrix747 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix747 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix747 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix747 (0 : Fin 4)) =
      Sparse.eval value239 (momentVector H) := by
    have heq : mergeFirst pivotMatrix747 (0 : Fin 4) = raw5478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix747 raw5478; decide +kernel
    rw [heq]
    exact (canonical5478 hH).trans (sound239 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix747 (1 : Fin 4)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix747 (1 : Fin 4) = raw5518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix747 raw5518; decide +kernel
    rw [heq]
    exact (canonical5518 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix747 (2 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix747 (2 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix747 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix747 (3 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix747 (3 : Fin 4) = raw5536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix747 raw5536; decide +kernel
    rw [heq]
    exact (canonical5536 hH).trans (sound255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node747 + (injectiveMoment H (mergeFirst pivotMatrix747 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix747 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix747 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix747 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value747, value239, value254, value255, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation748 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix748 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem sound748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node748 = Sparse.eval value748 (momentVector H) := by
  have heq : pivotMatrix748 = (fun u v => node748 (pivotPermutation748 u) v) := by apply Matrix.ext; unfold pivotMatrix748 node748 pivotPermutation748; decide +kernel
  have hmoment : injectiveMoment H node748 = injectiveMoment H pivotMatrix748 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix748 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix748 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix748 (0 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix748 (0 : Fin 4) = raw5962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix748 raw5962; decide +kernel
    rw [heq]
    exact (canonical5962 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix748 (1 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix748 (1 : Fin 4) = raw5543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix748 raw5543; decide +kernel
    rw [heq]
    exact (canonical5543 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix748 (2 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix748 (2 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix748 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix748 (3 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix748 (3 : Fin 4) = raw5530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix748 raw5530; decide +kernel
    rw [heq]
    exact (canonical5530 hH).trans (sound253 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node748 + (injectiveMoment H (mergeFirst pivotMatrix748 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix748 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix748 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix748 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value748, value253, value254, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation749 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix749 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem sound749 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node749 = Sparse.eval value749 (momentVector H) := by
  have heq : pivotMatrix749 = (fun u v => node749 (pivotPermutation749 u) v) := by apply Matrix.ext; unfold pivotMatrix749 node749 pivotPermutation749; decide +kernel
  have hmoment : injectiveMoment H node749 = injectiveMoment H pivotMatrix749 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix749 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix749 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix749 (0 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix749 (0 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix749 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix749 (1 : Fin 4)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix749 (1 : Fin 4) = raw5544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix749 raw5544; decide +kernel
    rw [heq]
    exact (canonical5544 hH).trans (sound256 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix749 (2 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix749 (2 : Fin 4) = raw5536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix749 raw5536; decide +kernel
    rw [heq]
    exact (canonical5536 hH).trans (sound255 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix749 (3 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix749 (3 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix749 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node749 + (injectiveMoment H (mergeFirst pivotMatrix749 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix749 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix749 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix749 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value749, value254, value255, value256, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation750 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix750 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem sound750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node750 = Sparse.eval value750 (momentVector H) := by
  have heq : pivotMatrix750 = (fun u v => node750 (pivotPermutation750 u) v) := by apply Matrix.ext; unfold pivotMatrix750 node750 pivotPermutation750; decide +kernel
  have hmoment : injectiveMoment H node750 = injectiveMoment H pivotMatrix750 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix750 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix750 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix750 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix750 (0 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix750 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix750 (1 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix750 (1 : Fin 3) = raw5574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix750 raw5574; decide +kernel
    rw [heq]
    exact (canonical5574 hH).trans (sound127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix750 (2 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix750 (2 : Fin 3) = raw5573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix750 raw5573; decide +kernel
    rw [heq]
    exact (canonical5573 hH).trans (sound124 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node750 + (injectiveMoment H (mergeFirst pivotMatrix750 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix750 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix750 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value750, value124, value127, value150, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation751 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix751 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -2, 5], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem sound751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node751 = Sparse.eval value751 (momentVector H) := by
  have heq : pivotMatrix751 = (fun u v => node751 (pivotPermutation751 u) v) := by apply Matrix.ext; unfold pivotMatrix751 node751 pivotPermutation751; decide +kernel
  have hmoment : injectiveMoment H node751 = injectiveMoment H pivotMatrix751 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix751 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix751 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix751 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix751 (0 : Fin 3) = raw5637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix751 raw5637; decide +kernel
    rw [heq]
    exact (canonical5637 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix751 (1 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix751 (1 : Fin 3) = raw5576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix751 raw5576; decide +kernel
    rw [heq]
    exact (canonical5576 hH).trans (sound127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix751 (2 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix751 (2 : Fin 3) = raw5575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix751 raw5575; decide +kernel
    rw [heq]
    exact (canonical5575 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node751 + (injectiveMoment H (mergeFirst pivotMatrix751 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix751 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix751 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value751, value120, value127, value145, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation752 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix752 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-2, 2, 1, -1], ![5, -2, -2, -1]]

theorem sound752 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node752 = Sparse.eval value752 (momentVector H) := by
  have heq : pivotMatrix752 = (fun u v => node752.transpose (pivotPermutation752 u) v) := by apply Matrix.ext; unfold pivotMatrix752 node752 pivotPermutation752; decide +kernel
  have hmoment : injectiveMoment H node752 = injectiveMoment H pivotMatrix752 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix752 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix752 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix752 (0 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix752 (0 : Fin 3) = raw339 := by apply Matrix.ext; unfold mergeFirst pivotMatrix752 raw339; decide +kernel
    rw [heq]
    exact (canonical339 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix752 (1 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix752 (1 : Fin 3) = raw3644 := by apply Matrix.ext; unfold mergeFirst pivotMatrix752 raw3644; decide +kernel
    rw [heq]
    exact (canonical3644 hH).trans (sound127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix752 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix752 (2 : Fin 3) = raw3646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix752 raw3646; decide +kernel
    rw [heq]
    exact (canonical3646 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node752 + (injectiveMoment H (mergeFirst pivotMatrix752 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix752 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix752 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value752, value127, value153, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation753 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix753 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-2, 2, -1, 1], ![5, -2, -1, -2]]

theorem sound753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node753 = Sparse.eval value753 (momentVector H) := by
  have heq : pivotMatrix753 = (fun u v => node753.transpose (pivotPermutation753 u) v) := by apply Matrix.ext; unfold pivotMatrix753 node753 pivotPermutation753; decide +kernel
  have hmoment : injectiveMoment H node753 = injectiveMoment H pivotMatrix753 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix753 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix753 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix753 (0 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix753 (0 : Fin 3) = raw355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix753 raw355; decide +kernel
    rw [heq]
    exact (canonical355 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix753 (1 : Fin 3)) =
      Sparse.eval value125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix753 (1 : Fin 3) = raw4164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix753 raw4164; decide +kernel
    rw [heq]
    exact (canonical4164 hH).trans (sound125 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix753 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix753 (2 : Fin 3) = raw4166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix753 raw4166; decide +kernel
    rw [heq]
    exact (canonical4166 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node753 + (injectiveMoment H (mergeFirst pivotMatrix753 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix753 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix753 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value753, value125, value146, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation754 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix754 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2]]

theorem sound754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node754 = Sparse.eval value754 (momentVector H) := by
  have heq : pivotMatrix754 = (fun u v => node754 (pivotPermutation754 u) v) := by apply Matrix.ext; unfold pivotMatrix754 node754 pivotPermutation754; decide +kernel
  have hmoment : injectiveMoment H node754 = injectiveMoment H pivotMatrix754 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix754 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix754 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix754 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix754 (0 : Fin 3) = raw8021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix754 raw8021; decide +kernel
    rw [heq]
    exact (canonical8021 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix754 (1 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix754 (1 : Fin 3) = raw5577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix754 raw5577; decide +kernel
    rw [heq]
    exact (canonical5577 hH).trans (sound120 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix754 (2 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix754 (2 : Fin 3) = raw5569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix754 raw5569; decide +kernel
    rw [heq]
    exact (canonical5569 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node754 + (injectiveMoment H (mergeFirst pivotMatrix754 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix754 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix754 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value754, value120, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation755 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix755 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2]]

theorem sound755 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node755 = Sparse.eval value755 (momentVector H) := by
  have heq : pivotMatrix755 = (fun u v => node755 (pivotPermutation755 u) v) := by apply Matrix.ext; unfold pivotMatrix755 node755 pivotPermutation755; decide +kernel
  have hmoment : injectiveMoment H node755 = injectiveMoment H pivotMatrix755 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix755 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix755 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix755 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix755 (0 : Fin 3) = raw8024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix755 raw8024; decide +kernel
    rw [heq]
    exact (canonical8024 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix755 (1 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix755 (1 : Fin 3) = raw5578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix755 raw5578; decide +kernel
    rw [heq]
    exact (canonical5578 hH).trans (sound124 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix755 (2 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix755 (2 : Fin 3) = raw5573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix755 raw5573; decide +kernel
    rw [heq]
    exact (canonical5573 hH).trans (sound124 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node755 + (injectiveMoment H (mergeFirst pivotMatrix755 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix755 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix755 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value755, value124, value35, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation756 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix756 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 1, 2], ![-1, 2, 1, -2], ![4, -1, -2, -1]]

theorem sound756 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node756 = Sparse.eval value756 (momentVector H) := by
  have heq : pivotMatrix756 = (fun u v => node756.transpose (pivotPermutation756 u) v) := by apply Matrix.ext; unfold pivotMatrix756 node756 pivotPermutation756; decide +kernel
  have hmoment : injectiveMoment H node756 = injectiveMoment H pivotMatrix756 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix756 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix756 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix756 (0 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix756 (0 : Fin 3) = raw261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix756 raw261; decide +kernel
    rw [heq]
    exact (canonical261 hH).trans (sound161 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix756 (1 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix756 (1 : Fin 3) = raw2134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix756 raw2134; decide +kernel
    rw [heq]
    exact (canonical2134 hH).trans (sound134 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix756 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix756 (2 : Fin 3) = raw2146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix756 raw2146; decide +kernel
    rw [heq]
    exact (canonical2146 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node756 + (injectiveMoment H (mergeFirst pivotMatrix756 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix756 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix756 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value756, value111, value134, value161, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation757 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix757 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![-1, 2, -2, 1], ![4, -1, 0, -3]]

theorem sound757 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node757 = Sparse.eval value757 (momentVector H) := by
  have heq : pivotMatrix757 = (fun u v => node757.transpose (pivotPermutation757 u) v) := by apply Matrix.ext; unfold pivotMatrix757 node757 pivotPermutation757; decide +kernel
  have hmoment : injectiveMoment H node757 = injectiveMoment H pivotMatrix757 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix757 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix757 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix757 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix757 (0 : Fin 3) = raw263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix757 raw263; decide +kernel
    rw [heq]
    exact (canonical263 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix757 (1 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix757 (1 : Fin 3) = raw2523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix757 raw2523; decide +kernel
    rw [heq]
    exact (canonical2523 hH).trans (sound135 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix757 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix757 (2 : Fin 3) = raw2528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix757 raw2528; decide +kernel
    rw [heq]
    exact (canonical2528 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node757 + (injectiveMoment H (mergeFirst pivotMatrix757 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix757 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix757 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value757, value111, value135, value191, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation758 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix758 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![-1, 2, 1, -2], ![4, -1, -3, 0]]

theorem sound758 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node758 = Sparse.eval value758 (momentVector H) := by
  have heq : pivotMatrix758 = (fun u v => node758.transpose (pivotPermutation758 u) v) := by apply Matrix.ext; unfold pivotMatrix758 node758 pivotPermutation758; decide +kernel
  have hmoment : injectiveMoment H node758 = injectiveMoment H pivotMatrix758 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix758 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix758 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix758 (0 : Fin 3)) =
      Sparse.eval value191 (momentVector H) := by
    have heq : mergeFirst pivotMatrix758 (0 : Fin 3) = raw264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix758 raw264; decide +kernel
    rw [heq]
    exact (canonical264 hH).trans (sound191 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix758 (1 : Fin 3)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix758 (1 : Fin 3) = raw2525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix758 raw2525; decide +kernel
    rw [heq]
    exact (canonical2525 hH).trans (sound132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix758 (2 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix758 (2 : Fin 3) = raw2529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix758 raw2529; decide +kernel
    rw [heq]
    exact (canonical2529 hH).trans (sound159 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node758 + (injectiveMoment H (mergeFirst pivotMatrix758 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix758 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix758 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value758, value132, value159, value191, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation759 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix759 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 3, 0], ![-1, 2, -2, 1], ![4, -1, -1, -2]]

theorem sound759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node759 = Sparse.eval value759 (momentVector H) := by
  have heq : pivotMatrix759 = (fun u v => node759.transpose (pivotPermutation759 u) v) := by apply Matrix.ext; unfold pivotMatrix759 node759 pivotPermutation759; decide +kernel
  have hmoment : injectiveMoment H node759 = injectiveMoment H pivotMatrix759 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix759 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix759 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix759 (0 : Fin 3)) =
      Sparse.eval value161 (momentVector H) := by
    have heq : mergeFirst pivotMatrix759 (0 : Fin 3) = raw267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix759 raw267; decide +kernel
    rw [heq]
    exact (canonical267 hH).trans (sound161 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix759 (1 : Fin 3)) =
      Sparse.eval value112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix759 (1 : Fin 3) = raw2867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix759 raw2867; decide +kernel
    rw [heq]
    exact (canonical2867 hH).trans (sound112 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix759 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix759 (2 : Fin 3) = raw2868 := by apply Matrix.ext; unfold mergeFirst pivotMatrix759 raw2868; decide +kernel
    rw [heq]
    exact (canonical2868 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node759 + (injectiveMoment H (mergeFirst pivotMatrix759 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix759 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix759 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value759, value109, value112, value161, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation760 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix760 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem sound760 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node760 = Sparse.eval value760 (momentVector H) := by
  have heq : pivotMatrix760 = (fun u v => node760 (pivotPermutation760 u) v) := by apply Matrix.ext; unfold pivotMatrix760 node760 pivotPermutation760; decide +kernel
  have hmoment : injectiveMoment H node760 = injectiveMoment H pivotMatrix760 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix760 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix760 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix760 (0 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix760 (0 : Fin 3) = raw5569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix760 raw5569; decide +kernel
    rw [heq]
    exact (canonical5569 hH).trans (sound120 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix760 (1 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix760 (1 : Fin 3) = raw5603 := by apply Matrix.ext; unfold mergeFirst pivotMatrix760 raw5603; decide +kernel
    rw [heq]
    exact (canonical5603 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix760 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix760 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix760 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node760 + (injectiveMoment H (mergeFirst pivotMatrix760 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix760 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix760 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value760, value120, value146, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation761 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix761 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 1, 1, -3]]

theorem sound761 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node761 = Sparse.eval value761 (momentVector H) := by
  have heq : pivotMatrix761 = (fun u v => node761 (pivotPermutation761 u) v) := by apply Matrix.ext; unfold pivotMatrix761 node761 pivotPermutation761; decide +kernel
  have hmoment : injectiveMoment H node761 = injectiveMoment H pivotMatrix761 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix761 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix761 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix761 (0 : Fin 3)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix761 (0 : Fin 3) = raw5573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix761 raw5573; decide +kernel
    rw [heq]
    exact (canonical5573 hH).trans (sound124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix761 (1 : Fin 3)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix761 (1 : Fin 3) = raw5628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix761 raw5628; decide +kernel
    rw [heq]
    exact (canonical5628 hH).trans (sound253 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix761 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix761 (2 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix761 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node761 + (injectiveMoment H (mergeFirst pivotMatrix761 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix761 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix761 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value761, value124, value150, value253, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation762 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix762 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem sound762 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node762 = Sparse.eval value762 (momentVector H) := by
  have heq : pivotMatrix762 = (fun u v => node762 (pivotPermutation762 u) v) := by apply Matrix.ext; unfold pivotMatrix762 node762 pivotPermutation762; decide +kernel
  have hmoment : injectiveMoment H node762 = injectiveMoment H pivotMatrix762 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix762 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix762 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix762 (0 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix762 (0 : Fin 3) = raw5574 := by apply Matrix.ext; unfold mergeFirst pivotMatrix762 raw5574; decide +kernel
    rw [heq]
    exact (canonical5574 hH).trans (sound127 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix762 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix762 (1 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix762 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix762 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix762 (2 : Fin 3) = raw5633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix762 raw5633; decide +kernel
    rw [heq]
    exact (canonical5633 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node762 + (injectiveMoment H (mergeFirst pivotMatrix762 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix762 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix762 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value762, value127, value150, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation763 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix763 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem sound763 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node763 = Sparse.eval value763 (momentVector H) := by
  have heq : pivotMatrix763 = (fun u v => node763 (pivotPermutation763 u) v) := by apply Matrix.ext; unfold pivotMatrix763 node763 pivotPermutation763; decide +kernel
  have hmoment : injectiveMoment H node763 = injectiveMoment H pivotMatrix763 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix763 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix763 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix763 (0 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix763 (0 : Fin 3) = raw5575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix763 raw5575; decide +kernel
    rw [heq]
    exact (canonical5575 hH).trans (sound120 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix763 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix763 (1 : Fin 3) = raw5636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix763 raw5636; decide +kernel
    rw [heq]
    exact (canonical5636 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix763 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix763 (2 : Fin 3) = raw5637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix763 raw5637; decide +kernel
    rw [heq]
    exact (canonical5637 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node763 + (injectiveMoment H (mergeFirst pivotMatrix763 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix763 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix763 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value763, value120, value145, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation764 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix764 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, -1, 4], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem sound764 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node764 = Sparse.eval value764 (momentVector H) := by
  have heq : pivotMatrix764 = (fun u v => node764 (pivotPermutation764 u) v) := by apply Matrix.ext; unfold pivotMatrix764 node764 pivotPermutation764; decide +kernel
  have hmoment : injectiveMoment H node764 = injectiveMoment H pivotMatrix764 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix764 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix764 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix764 (0 : Fin 3)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix764 (0 : Fin 3) = raw5576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix764 raw5576; decide +kernel
    rw [heq]
    exact (canonical5576 hH).trans (sound127 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix764 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix764 (1 : Fin 3) = raw5637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix764 raw5637; decide +kernel
    rw [heq]
    exact (canonical5637 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix764 (2 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix764 (2 : Fin 3) = raw5638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix764 raw5638; decide +kernel
    rw [heq]
    exact (canonical5638 hH).trans (sound254 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node764 + (injectiveMoment H (mergeFirst pivotMatrix764 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix764 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix764 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value764, value127, value145, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation765 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix765 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 2, -2, -1]]

theorem sound765 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node765 = Sparse.eval value765 (momentVector H) := by
  have heq : pivotMatrix765 = (fun u v => node765 (pivotPermutation765 u) v) := by apply Matrix.ext; unfold pivotMatrix765 node765 pivotPermutation765; decide +kernel
  have hmoment : injectiveMoment H node765 = injectiveMoment H pivotMatrix765 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix765 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix765 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix765 (0 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix765 (0 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix765 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix765 (1 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix765 (1 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix765 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix765 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix765 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix765 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node765 + (injectiveMoment H (mergeFirst pivotMatrix765 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix765 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix765 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value765, value146, value177, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation766 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix766 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem sound766 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node766 = Sparse.eval value766 (momentVector H) := by
  have heq : pivotMatrix766 = (fun u v => node766 (pivotPermutation766 u) v) := by apply Matrix.ext; unfold pivotMatrix766 node766 pivotPermutation766; decide +kernel
  have hmoment : injectiveMoment H node766 = injectiveMoment H pivotMatrix766 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix766 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix766 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix766 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix766 (0 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix766 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix766 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix766 (1 : Fin 3) = raw5633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix766 raw5633; decide +kernel
    rw [heq]
    exact (canonical5633 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix766 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix766 (2 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix766 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node766 + (injectiveMoment H (mergeFirst pivotMatrix766 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix766 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix766 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value766, value150, value181, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation767 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix767 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem sound767 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node767 = Sparse.eval value767 (momentVector H) := by
  have heq : pivotMatrix767 = (fun u v => node767 (pivotPermutation767 u) v) := by apply Matrix.ext; unfold pivotMatrix767 node767 pivotPermutation767; decide +kernel
  have hmoment : injectiveMoment H node767 = injectiveMoment H pivotMatrix767 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix767 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix767 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix767 (0 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix767 (0 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix767 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix767 (1 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix767 (1 : Fin 3) = raw5634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix767 raw5634; decide +kernel
    rw [heq]
    exact (canonical5634 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix767 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix767 (2 : Fin 3) = raw5633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix767 raw5633; decide +kernel
    rw [heq]
    exact (canonical5633 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node767 + (injectiveMoment H (mergeFirst pivotMatrix767 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix767 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix767 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value767, value190, value215, value246, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
