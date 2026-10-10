import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical210
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical257

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation832 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix832 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3]]

theorem sound832 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node832 = Sparse.eval value832 (momentVector H) := by
  have heq : pivotMatrix832 = (fun u v => node832 (pivotPermutation832 u) v) := by apply Matrix.ext; unfold pivotMatrix832 node832 pivotPermutation832; decide +kernel
  have hmoment : injectiveMoment H node832 = injectiveMoment H pivotMatrix832 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix832 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix832 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix832 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix832 (0 : Fin 3) = raw8120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix832 raw8120; decide +kernel
    rw [heq]
    exact (canonical8120 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix832 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix832 (1 : Fin 3) = raw5803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix832 raw5803; decide +kernel
    rw [heq]
    exact (canonical5803 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix832 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix832 (2 : Fin 3) = raw5741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix832 raw5741; decide +kernel
    rw [heq]
    exact (canonical5741 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node832 + (injectiveMoment H (mergeFirst pivotMatrix832 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix832 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix832 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value832, value146, value226, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation833 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix833 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

theorem sound833 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node833 = Sparse.eval value833 (momentVector H) := by
  have heq : pivotMatrix833 = (fun u v => node833 (pivotPermutation833 u) v) := by apply Matrix.ext; unfold pivotMatrix833 node833 pivotPermutation833; decide +kernel
  have hmoment : injectiveMoment H node833 = injectiveMoment H pivotMatrix833 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix833 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix833 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix833 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix833 (0 : Fin 3) = raw8069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix833 raw8069; decide +kernel
    rw [heq]
    exact (canonical8069 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix833 (1 : Fin 3)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix833 (1 : Fin 3) = raw5802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix833 raw5802; decide +kernel
    rw [heq]
    exact (canonical5802 hH).trans (sound102 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix833 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix833 (2 : Fin 3) = raw5741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix833 raw5741; decide +kernel
    rw [heq]
    exact (canonical5741 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node833 + (injectiveMoment H (mergeFirst pivotMatrix833 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix833 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix833 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value833, value102, value146, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation834 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix834 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

theorem sound834 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node834 = Sparse.eval value834 (momentVector H) := by
  have heq : pivotMatrix834 = (fun u v => node834 (pivotPermutation834 u) v) := by apply Matrix.ext; unfold pivotMatrix834 node834 pivotPermutation834; decide +kernel
  have hmoment : injectiveMoment H node834 = injectiveMoment H pivotMatrix834 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix834 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix834 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix834 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix834 (0 : Fin 3) = raw5705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix834 raw5705; decide +kernel
    rw [heq]
    exact (canonical5705 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix834 (1 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix834 (1 : Fin 3) = raw5775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix834 raw5775; decide +kernel
    rw [heq]
    exact (canonical5775 hH).trans (sound106 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix834 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix834 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix834 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node834 + (injectiveMoment H (mergeFirst pivotMatrix834 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix834 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix834 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value834, value106, value206, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation835 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix835 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem sound835 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node835 = Sparse.eval value835 (momentVector H) := by
  have heq : pivotMatrix835 = (fun u v => node835 (pivotPermutation835 u) v) := by apply Matrix.ext; unfold pivotMatrix835 node835 pivotPermutation835; decide +kernel
  have hmoment : injectiveMoment H node835 = injectiveMoment H pivotMatrix835 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix835 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix835 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix835 (0 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix835 (0 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix835 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix835 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix835 (1 : Fin 3) = raw5790 := by apply Matrix.ext; unfold mergeFirst pivotMatrix835 raw5790; decide +kernel
    rw [heq]
    exact (canonical5790 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix835 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix835 (2 : Fin 3) = raw5793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix835 raw5793; decide +kernel
    rw [heq]
    exact (canonical5793 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node835 + (injectiveMoment H (mergeFirst pivotMatrix835 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix835 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix835 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value835, value181, value210, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation836 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix836 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem sound836 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node836 = Sparse.eval value836 (momentVector H) := by
  have heq : pivotMatrix836 = (fun u v => node836 (pivotPermutation836 u) v) := by apply Matrix.ext; unfold pivotMatrix836 node836 pivotPermutation836; decide +kernel
  have hmoment : injectiveMoment H node836 = injectiveMoment H pivotMatrix836 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix836 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix836 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix836 (0 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix836 (0 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix836 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix836 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix836 (1 : Fin 3) = raw5793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix836 raw5793; decide +kernel
    rw [heq]
    exact (canonical5793 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix836 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix836 (2 : Fin 3) = raw5795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix836 raw5795; decide +kernel
    rw [heq]
    exact (canonical5795 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node836 + (injectiveMoment H (mergeFirst pivotMatrix836 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix836 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix836 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value836, value109, value210, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation837 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix837 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound837 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node837 = Sparse.eval value837 (momentVector H) := by
  have heq : pivotMatrix837 = (fun u v => node837 (pivotPermutation837 u) v) := by apply Matrix.ext; unfold pivotMatrix837 node837 pivotPermutation837; decide +kernel
  have hmoment : injectiveMoment H node837 = injectiveMoment H pivotMatrix837 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix837 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix837 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix837 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix837 (0 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix837 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix837 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix837 (1 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix837 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix837 (2 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix837 (2 : Fin 3) = raw5798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix837 raw5798; decide +kernel
    rw [heq]
    exact (canonical5798 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node837 + (injectiveMoment H (mergeFirst pivotMatrix837 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix837 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix837 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value837, value185, value203, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation838 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix838 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem sound838 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node838 = Sparse.eval value838 (momentVector H) := by
  have heq : pivotMatrix838 = (fun u v => node838 (pivotPermutation838 u) v) := by apply Matrix.ext; unfold pivotMatrix838 node838 pivotPermutation838; decide +kernel
  have hmoment : injectiveMoment H node838 = injectiveMoment H pivotMatrix838 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix838 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix838 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix838 (0 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix838 (0 : Fin 3) = raw5837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix838 raw5837; decide +kernel
    rw [heq]
    exact (canonical5837 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix838 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix838 (1 : Fin 3) = raw5786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix838 raw5786; decide +kernel
    rw [heq]
    exact (canonical5786 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix838 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix838 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix838 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node838 + (injectiveMoment H (mergeFirst pivotMatrix838 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix838 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix838 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value838, value210, value229, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation839 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix839 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem sound839 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node839 = Sparse.eval value839 (momentVector H) := by
  have heq : pivotMatrix839 = (fun u v => node839 (pivotPermutation839 u) v) := by apply Matrix.ext; unfold pivotMatrix839 node839 pivotPermutation839; decide +kernel
  have hmoment : injectiveMoment H node839 = injectiveMoment H pivotMatrix839 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix839 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix839 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix839 (0 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix839 (0 : Fin 3) = raw5842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix839 raw5842; decide +kernel
    rw [heq]
    exact (canonical5842 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix839 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix839 (1 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix839 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix839 (2 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix839 (2 : Fin 3) = raw5796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix839 raw5796; decide +kernel
    rw [heq]
    exact (canonical5796 hH).trans (sound107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node839 + (injectiveMoment H (mergeFirst pivotMatrix839 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix839 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix839 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value839, value107, value203, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation840 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix840 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem sound840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node840 = Sparse.eval value840 (momentVector H) := by
  have heq : pivotMatrix840 = (fun u v => node840 (pivotPermutation840 u) v) := by apply Matrix.ext; unfold pivotMatrix840 node840 pivotPermutation840; decide +kernel
  have hmoment : injectiveMoment H node840 = injectiveMoment H pivotMatrix840 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix840 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix840 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix840 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix840 (0 : Fin 3) = raw5843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix840 raw5843; decide +kernel
    rw [heq]
    exact (canonical5843 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix840 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix840 (1 : Fin 3) = raw5800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix840 raw5800; decide +kernel
    rw [heq]
    exact (canonical5800 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix840 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix840 (2 : Fin 3) = raw5799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix840 raw5799; decide +kernel
    rw [heq]
    exact (canonical5799 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node840 + (injectiveMoment H (mergeFirst pivotMatrix840 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix840 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix840 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value840, value203, value226, value291, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation841 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 2, -3, 0], ![2, -2, 2, -2]]

theorem sound841 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node841 = Sparse.eval value841 (momentVector H) := by
  have heq : pivotMatrix841 = (fun u v => node841.transpose (pivotPermutation841 u) v) := by apply Matrix.ext; unfold pivotMatrix841 node841 pivotPermutation841; decide +kernel
  have hmoment : injectiveMoment H node841 = injectiveMoment H pivotMatrix841 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix841 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix841 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix841 (0 : Fin 3)) =
      Sparse.eval value110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix841 (0 : Fin 3) = raw352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix841 raw352; decide +kernel
    rw [heq]
    exact (canonical352 hH).trans (sound110 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix841 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix841 (1 : Fin 3) = raw3845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix841 raw3845; decide +kernel
    rw [heq]
    exact (canonical3845 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix841 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix841 (2 : Fin 3) = raw3862 := by apply Matrix.ext; unfold mergeFirst pivotMatrix841 raw3862; decide +kernel
    rw [heq]
    exact (canonical3862 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node841 + (injectiveMoment H (mergeFirst pivotMatrix841 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix841 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix841 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value841, value110, value212, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation842 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, 2, -2, -1], ![2, -2, 1, -1]]

theorem sound842 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node842 = Sparse.eval value842 (momentVector H) := by
  have heq : pivotMatrix842 = (fun u v => node842.transpose (pivotPermutation842 u) v) := by apply Matrix.ext; unfold pivotMatrix842 node842 pivotPermutation842; decide +kernel
  have hmoment : injectiveMoment H node842 = injectiveMoment H pivotMatrix842 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix842 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix842 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix842 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix842 (0 : Fin 3) = raw353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix842 raw353; decide +kernel
    rw [heq]
    exact (canonical353 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix842 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix842 (1 : Fin 3) = raw3847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix842 raw3847; decide +kernel
    rw [heq]
    exact (canonical3847 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix842 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix842 (2 : Fin 3) = raw3863 := by apply Matrix.ext; unfold mergeFirst pivotMatrix842 raw3863; decide +kernel
    rw [heq]
    exact (canonical3863 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node842 + (injectiveMoment H (mergeFirst pivotMatrix842 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix842 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix842 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value842, value111, value203, value210, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation843 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix843 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1]]

theorem sound843 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node843 = Sparse.eval value843 (momentVector H) := by
  have heq : pivotMatrix843 = (fun u v => node843 (pivotPermutation843 u) v) := by apply Matrix.ext; unfold pivotMatrix843 node843 pivotPermutation843; decide +kernel
  have hmoment : injectiveMoment H node843 = injectiveMoment H pivotMatrix843 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix843 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix843 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix843 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix843 (0 : Fin 3) = raw8155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix843 raw8155; decide +kernel
    rw [heq]
    exact (canonical8155 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix843 (1 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix843 (1 : Fin 3) = raw5804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix843 raw5804; decide +kernel
    rw [heq]
    exact (canonical5804 hH).trans (sound107 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix843 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix843 (2 : Fin 3) = raw5774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix843 raw5774; decide +kernel
    rw [heq]
    exact (canonical5774 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node843 + (injectiveMoment H (mergeFirst pivotMatrix843 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix843 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix843 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value843, value107, value177, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation844 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, 2, -1, -2], ![2, -2, -1, 1]]

theorem sound844 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node844 = Sparse.eval value844 (momentVector H) := by
  have heq : pivotMatrix844 = (fun u v => node844.transpose (pivotPermutation844 u) v) := by apply Matrix.ext; unfold pivotMatrix844 node844 pivotPermutation844; decide +kernel
  have hmoment : injectiveMoment H node844 = injectiveMoment H pivotMatrix844 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix844 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix844 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix844 (0 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix844 (0 : Fin 3) = raw367 := by apply Matrix.ext; unfold mergeFirst pivotMatrix844 raw367; decide +kernel
    rw [heq]
    exact (canonical367 hH).trans (sound111 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix844 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix844 (1 : Fin 3) = raw4196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix844 raw4196; decide +kernel
    rw [heq]
    exact (canonical4196 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix844 (2 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix844 (2 : Fin 3) = raw4210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix844 raw4210; decide +kernel
    rw [heq]
    exact (canonical4210 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node844 + (injectiveMoment H (mergeFirst pivotMatrix844 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix844 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix844 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value844, value111, value203, value224, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation845 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix845 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem sound845 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node845 = Sparse.eval value845 (momentVector H) := by
  have heq : pivotMatrix845 = (fun u v => node845 (pivotPermutation845 u) v) := by apply Matrix.ext; unfold pivotMatrix845 node845 pivotPermutation845; decide +kernel
  have hmoment : injectiveMoment H node845 = injectiveMoment H pivotMatrix845 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix845 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix845 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix845 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix845 (0 : Fin 3) = raw6693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix845 raw6693; decide +kernel
    rw [heq]
    exact (canonical6693 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix845 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix845 (1 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix845 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix845 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix845 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix845 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node845 + (injectiveMoment H (mergeFirst pivotMatrix845 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix845 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix845 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value845, value203, value229, value230, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation846 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix846 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2]]

theorem sound846 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node846 = Sparse.eval value846 (momentVector H) := by
  have heq : pivotMatrix846 = (fun u v => node846 (pivotPermutation846 u) v) := by apply Matrix.ext; unfold pivotMatrix846 node846 pivotPermutation846; decide +kernel
  have hmoment : injectiveMoment H node846 = injectiveMoment H pivotMatrix846 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix846 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix846 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix846 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix846 (0 : Fin 3) = raw8157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix846 raw8157; decide +kernel
    rw [heq]
    exact (canonical8157 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix846 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix846 (1 : Fin 3) = raw5806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix846 raw5806; decide +kernel
    rw [heq]
    exact (canonical5806 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix846 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix846 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix846 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node846 + (injectiveMoment H (mergeFirst pivotMatrix846 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix846 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix846 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value846, value210, value229, value44, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation847 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix847 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

theorem sound847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node847 = Sparse.eval value847 (momentVector H) := by
  have heq : pivotMatrix847 = (fun u v => node847 (pivotPermutation847 u) v) := by apply Matrix.ext; unfold pivotMatrix847 node847 pivotPermutation847; decide +kernel
  have hmoment : injectiveMoment H node847 = injectiveMoment H pivotMatrix847 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix847 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix847 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix847 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix847 (0 : Fin 3) = raw8099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix847 raw8099; decide +kernel
    rw [heq]
    exact (canonical8099 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix847 (1 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix847 (1 : Fin 3) = raw5805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix847 raw5805; decide +kernel
    rw [heq]
    exact (canonical5805 hH).trans (sound109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix847 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix847 (2 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix847 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node847 + (injectiveMoment H (mergeFirst pivotMatrix847 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix847 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix847 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value847, value109, value229, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation848 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![1, -2, 3, -2], ![2, 1, -4, 1]]

theorem sound848 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node848 = Sparse.eval value848 (momentVector H) := by
  have heq : pivotMatrix848 = (fun u v => node848.transpose (pivotPermutation848 u) v) := by apply Matrix.ext; unfold pivotMatrix848 node848 pivotPermutation848; decide +kernel
  have hmoment : injectiveMoment H node848 = injectiveMoment H pivotMatrix848 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix848 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix848 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix848 (0 : Fin 3)) =
      Sparse.eval value115 (momentVector H) := by
    have heq : mergeFirst pivotMatrix848 (0 : Fin 3) = raw595 := by apply Matrix.ext; unfold mergeFirst pivotMatrix848 raw595; decide +kernel
    rw [heq]
    exact (canonical595 hH).trans (sound115 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix848 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix848 (1 : Fin 3) = raw4982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix848 raw4982; decide +kernel
    rw [heq]
    exact (canonical4982 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix848 (2 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix848 (2 : Fin 3) = raw5049 := by apply Matrix.ext; unfold mergeFirst pivotMatrix848 raw5049; decide +kernel
    rw [heq]
    exact (canonical5049 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node848 + (injectiveMoment H (mergeFirst pivotMatrix848 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix848 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix848 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value848, value115, value206, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation849 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 2, -1], ![1, -2, 2, -1], ![2, 1, -4, 1]]

theorem sound849 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node849 = Sparse.eval value849 (momentVector H) := by
  have heq : pivotMatrix849 = (fun u v => node849.transpose (pivotPermutation849 u) v) := by apply Matrix.ext; unfold pivotMatrix849 node849 pivotPermutation849; decide +kernel
  have hmoment : injectiveMoment H node849 = injectiveMoment H pivotMatrix849 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix849 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix849 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix849 (0 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix849 (0 : Fin 3) = raw818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix849 raw818; decide +kernel
    rw [heq]
    exact (canonical818 hH).trans (sound106 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix849 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix849 (1 : Fin 3) = raw5054 := by apply Matrix.ext; unfold mergeFirst pivotMatrix849 raw5054; decide +kernel
    rw [heq]
    exact (canonical5054 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix849 (2 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix849 (2 : Fin 3) = raw5073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix849 raw5073; decide +kernel
    rw [heq]
    exact (canonical5073 hH).trans (sound134 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node849 + (injectiveMoment H (mergeFirst pivotMatrix849 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix849 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix849 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value849, value106, value134, value146, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation850 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix850 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 1, 2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem sound850 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node850 = Sparse.eval value850 (momentVector H) := by
  have heq : pivotMatrix850 = (fun u v => node850 (pivotPermutation850 u) v) := by apply Matrix.ext; unfold pivotMatrix850 node850 pivotPermutation850; decide +kernel
  have hmoment : injectiveMoment H node850 = injectiveMoment H pivotMatrix850 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix850 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix850 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix850 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix850 (0 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix850 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix850 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix850 (1 : Fin 3) = raw5800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix850 raw5800; decide +kernel
    rw [heq]
    exact (canonical5800 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix850 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix850 (2 : Fin 3) = raw5795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix850 raw5795; decide +kernel
    rw [heq]
    exact (canonical5795 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node850 + (injectiveMoment H (mergeFirst pivotMatrix850 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix850 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix850 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value850, value109, value185, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation851 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 2, -1], ![1, 1, -3, 1], ![2, -2, 1, -1]]

theorem sound851 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node851 = Sparse.eval value851 (momentVector H) := by
  have heq : pivotMatrix851 = (fun u v => node851.transpose (pivotPermutation851 u) v) := by apply Matrix.ext; unfold pivotMatrix851 node851 pivotPermutation851; decide +kernel
  have hmoment : injectiveMoment H node851 = injectiveMoment H pivotMatrix851 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix851 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix851 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix851 (0 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix851 (0 : Fin 3) = raw819 := by apply Matrix.ext; unfold mergeFirst pivotMatrix851 raw819; decide +kernel
    rw [heq]
    exact (canonical819 hH).trans (sound109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix851 (1 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix851 (1 : Fin 3) = raw5067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix851 raw5067; decide +kernel
    rw [heq]
    exact (canonical5067 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix851 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix851 (2 : Fin 3) = raw5074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix851 raw5074; decide +kernel
    rw [heq]
    exact (canonical5074 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node851 + (injectiveMoment H (mergeFirst pivotMatrix851 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix851 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix851 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value851, value109, value111, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation852 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 2, -1], ![1, 2, -2, -1], ![2, -3, 0, 1]]

theorem sound852 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node852 = Sparse.eval value852 (momentVector H) := by
  have heq : pivotMatrix852 = (fun u v => node852.transpose (pivotPermutation852 u) v) := by apply Matrix.ext; unfold pivotMatrix852 node852 pivotPermutation852; decide +kernel
  have hmoment : injectiveMoment H node852 = injectiveMoment H pivotMatrix852 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix852 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix852 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix852 (0 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix852 (0 : Fin 3) = raw820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix852 raw820; decide +kernel
    rw [heq]
    exact (canonical820 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix852 (1 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix852 (1 : Fin 3) = raw5068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix852 raw5068; decide +kernel
    rw [heq]
    exact (canonical5068 hH).trans (sound177 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix852 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix852 (2 : Fin 3) = raw5075 := by apply Matrix.ext; unfold mergeFirst pivotMatrix852 raw5075; decide +kernel
    rw [heq]
    exact (canonical5075 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node852 + (injectiveMoment H (mergeFirst pivotMatrix852 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix852 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix852 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value852, value107, value111, value177, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation853 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix853 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 2, 1], ![0, 0, -2, 2], ![1, 1, 0, -2]]

theorem sound853 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node853 = Sparse.eval value853 (momentVector H) := by
  have heq : pivotMatrix853 = (fun u v => node853 (pivotPermutation853 u) v) := by apply Matrix.ext; unfold pivotMatrix853 node853 pivotPermutation853; decide +kernel
  have hmoment : injectiveMoment H node853 = injectiveMoment H pivotMatrix853 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix853 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix853 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix853 (0 : Fin 3)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix853 (0 : Fin 3) = raw6928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix853 raw6928; decide +kernel
    rw [heq]
    exact (canonical6928 hH).trans (sound207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix853 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix853 (1 : Fin 3) = raw5837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix853 raw5837; decide +kernel
    rw [heq]
    exact (canonical5837 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix853 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix853 (2 : Fin 3) = raw5824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix853 raw5824; decide +kernel
    rw [heq]
    exact (canonical5824 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node853 + (injectiveMoment H (mergeFirst pivotMatrix853 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix853 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix853 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value853, value177, value207, value210, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation854 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix854 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2]]

theorem sound854 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node854 = Sparse.eval value854 (momentVector H) := by
  have heq : pivotMatrix854 = (fun u v => node854 (pivotPermutation854 u) v) := by apply Matrix.ext; unfold pivotMatrix854 node854 pivotPermutation854; decide +kernel
  have hmoment : injectiveMoment H node854 = injectiveMoment H pivotMatrix854 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix854 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix854 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix854 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix854 (0 : Fin 3) = raw8247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix854 raw8247; decide +kernel
    rw [heq]
    exact (canonical8247 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix854 (1 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix854 (1 : Fin 3) = raw5846 := by apply Matrix.ext; unfold mergeFirst pivotMatrix854 raw5846; decide +kernel
    rw [heq]
    exact (canonical5846 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix854 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix854 (2 : Fin 3) = raw5824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix854 raw5824; decide +kernel
    rw [heq]
    exact (canonical5824 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node854 + (injectiveMoment H (mergeFirst pivotMatrix854 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix854 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix854 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value854, value177, value203, value41, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation855 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix855 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3]]

theorem sound855 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node855 = Sparse.eval value855 (momentVector H) := by
  have heq : pivotMatrix855 = (fun u v => node855 (pivotPermutation855 u) v) := by apply Matrix.ext; unfold pivotMatrix855 node855 pivotPermutation855; decide +kernel
  have hmoment : injectiveMoment H node855 = injectiveMoment H pivotMatrix855 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix855 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix855 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix855 (0 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix855 (0 : Fin 4) = raw6734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix855 raw6734; decide +kernel
    rw [heq]
    exact (canonical6734 hH).trans (sound175 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix855 (1 : Fin 4)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix855 (1 : Fin 4) = raw5871 := by apply Matrix.ext; unfold mergeFirst pivotMatrix855 raw5871; decide +kernel
    rw [heq]
    exact (canonical5871 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix855 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix855 (2 : Fin 4) = raw5864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix855 raw5864; decide +kernel
    rw [heq]
    exact (canonical5864 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix855 (3 : Fin 4)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix855 (3 : Fin 4) = raw5863 := by apply Matrix.ext; unfold mergeFirst pivotMatrix855 raw5863; decide +kernel
    rw [heq]
    exact (canonical5863 hH).trans (sound241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node855 + (injectiveMoment H (mergeFirst pivotMatrix855 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix855 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix855 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix855 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value855, value168, value175, value241, value258, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation856 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix856 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

theorem sound856 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node856 = Sparse.eval value856 (momentVector H) := by
  have heq : pivotMatrix856 = (fun u v => node856 (pivotPermutation856 u) v) := by apply Matrix.ext; unfold pivotMatrix856 node856 pivotPermutation856; decide +kernel
  have hmoment : injectiveMoment H node856 = injectiveMoment H pivotMatrix856 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix856 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix856 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix856 (0 : Fin 4)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (0 : Fin 4) = raw6735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw6735; decide +kernel
    rw [heq]
    exact (canonical6735 hH).trans (sound275 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix856 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (1 : Fin 4) = raw5872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5872; decide +kernel
    rw [heq]
    exact (canonical5872 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix856 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix856 (3 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (3 : Fin 4) = raw5864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5864; decide +kernel
    rw [heq]
    exact (canonical5864 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node856 + (injectiveMoment H (mergeFirst pivotMatrix856 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value856, value175, value258, value275, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation857 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix857 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 2, -3]]

theorem sound857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node857 = Sparse.eval value857 (momentVector H) := by
  have heq : pivotMatrix857 = (fun u v => node857 (pivotPermutation857 u) v) := by apply Matrix.ext; unfold pivotMatrix857 node857 pivotPermutation857; decide +kernel
  have hmoment : injectiveMoment H node857 = injectiveMoment H pivotMatrix857 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix857 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix857 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix857 (0 : Fin 4)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix857 (0 : Fin 4) = raw7989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix857 raw7989; decide +kernel
    rw [heq]
    exact (canonical7989 hH).trans (sound265 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix857 (1 : Fin 4)) =
      Sparse.eval value264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix857 (1 : Fin 4) = raw5913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix857 raw5913; decide +kernel
    rw [heq]
    exact (canonical5913 hH).trans (sound264 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix857 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix857 (2 : Fin 4) = raw5864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix857 raw5864; decide +kernel
    rw [heq]
    exact (canonical5864 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix857 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix857 (3 : Fin 4) = raw5857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix857 raw5857; decide +kernel
    rw [heq]
    exact (canonical5857 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node857 + (injectiveMoment H (mergeFirst pivotMatrix857 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix857 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix857 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix857 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value857, value167, value258, value264, value265, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation858 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix858 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

theorem sound858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node858 = Sparse.eval value858 (momentVector H) := by
  have heq : pivotMatrix858 = (fun u v => node858 (pivotPermutation858 u) v) := by apply Matrix.ext; unfold pivotMatrix858 node858 pivotPermutation858; decide +kernel
  have hmoment : injectiveMoment H node858 = injectiveMoment H pivotMatrix858 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix858 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix858 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix858 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (0 : Fin 4) = raw8160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw8160; decide +kernel
    rw [heq]
    exact (canonical8160 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix858 (1 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (1 : Fin 4) = raw5937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5937; decide +kernel
    rw [heq]
    exact (canonical5937 hH).trans (sound268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix858 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix858 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (3 : Fin 4) = raw5857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5857; decide +kernel
    rw [heq]
    exact (canonical5857 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node858 + (injectiveMoment H (mergeFirst pivotMatrix858 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value858, value167, value258, value268, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation859 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix859 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 1, -2]]

theorem sound859 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node859 = Sparse.eval value859 (momentVector H) := by
  have heq : pivotMatrix859 = (fun u v => node859 (pivotPermutation859 u) v) := by apply Matrix.ext; unfold pivotMatrix859 node859 pivotPermutation859; decide +kernel
  have hmoment : injectiveMoment H node859 = injectiveMoment H pivotMatrix859 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix859 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix859 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix859 (0 : Fin 4)) =
      Sparse.eval value277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix859 (0 : Fin 4) = raw7990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix859 raw7990; decide +kernel
    rw [heq]
    exact (canonical7990 hH).trans (sound277 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix859 (1 : Fin 4)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix859 (1 : Fin 4) = raw5914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix859 raw5914; decide +kernel
    rw [heq]
    exact (canonical5914 hH).trans (sound265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix859 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix859 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix859 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix859 (3 : Fin 4)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix859 (3 : Fin 4) = raw5860 := by apply Matrix.ext; unfold mergeFirst pivotMatrix859 raw5860; decide +kernel
    rw [heq]
    exact (canonical5860 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node859 + (injectiveMoment H (mergeFirst pivotMatrix859 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix859 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix859 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix859 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value859, value196, value258, value265, value277, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation860 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix860 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

theorem sound860 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node860 = Sparse.eval value860 (momentVector H) := by
  have heq : pivotMatrix860 = (fun u v => node860 (pivotPermutation860 u) v) := by apply Matrix.ext; unfold pivotMatrix860 node860 pivotPermutation860; decide +kernel
  have hmoment : injectiveMoment H node860 = injectiveMoment H pivotMatrix860 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix860 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix860 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix860 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix860 (0 : Fin 4) = raw8161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix860 raw8161; decide +kernel
    rw [heq]
    exact (canonical8161 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix860 (1 : Fin 4)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix860 (1 : Fin 4) = raw5940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix860 raw5940; decide +kernel
    rw [heq]
    exact (canonical5940 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix860 (2 : Fin 4)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix860 (2 : Fin 4) = raw5866 := by apply Matrix.ext; unfold mergeFirst pivotMatrix860 raw5866; decide +kernel
    rw [heq]
    exact (canonical5866 hH).trans (sound241 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix860 (3 : Fin 4)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix860 (3 : Fin 4) = raw5860 := by apply Matrix.ext; unfold mergeFirst pivotMatrix860 raw5860; decide +kernel
    rw [heq]
    exact (canonical5860 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node860 + (injectiveMoment H (mergeFirst pivotMatrix860 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix860 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix860 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix860 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value860, value196, value241, value269, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation861 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix861 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-1, -2, 3], ![-1, -1, 2], ![0, 4, -4], ![1, 0, -1]]

theorem sound861 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node861 = Sparse.eval value861 (momentVector H) := by
  have heq : pivotMatrix861 = (fun u v => node861 (pivotPermutation861 u) v) := by apply Matrix.ext; unfold pivotMatrix861 node861 pivotPermutation861; decide +kernel
  have hmoment : injectiveMoment H node861 = injectiveMoment H pivotMatrix861 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix861 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix861 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix861 (0 : Fin 4)) =
      Sparse.eval value278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix861 (0 : Fin 4) = raw7991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix861 raw7991; decide +kernel
    rw [heq]
    exact (canonical7991 hH).trans (sound278 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix861 (1 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix861 (1 : Fin 4) = raw5915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix861 raw5915; decide +kernel
    rw [heq]
    exact (canonical5915 hH).trans (sound266 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix861 (2 : Fin 4)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix861 (2 : Fin 4) = raw5866 := by apply Matrix.ext; unfold mergeFirst pivotMatrix861 raw5866; decide +kernel
    rw [heq]
    exact (canonical5866 hH).trans (sound241 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix861 (3 : Fin 4)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix861 (3 : Fin 4) = raw5862 := by apply Matrix.ext; unfold mergeFirst pivotMatrix861 raw5862; decide +kernel
    rw [heq]
    exact (canonical5862 hH).trans (sound219 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node861 + (injectiveMoment H (mergeFirst pivotMatrix861 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix861 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix861 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix861 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value861, value219, value241, value266, value278, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation862 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound862 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node862 = Sparse.eval value862 (momentVector H) := by
  have heq : pivotMatrix862 = (fun u v => node862 (pivotPermutation862 u) v) := by apply Matrix.ext; unfold pivotMatrix862 node862 pivotPermutation862; decide +kernel
  have hmoment : injectiveMoment H node862 = injectiveMoment H pivotMatrix862 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix862 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix862 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix862 (0 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix862 (0 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix862 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix862 (1 : Fin 4)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix862 (1 : Fin 4) = raw5877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix862 raw5877; decide +kernel
    rw [heq]
    exact (canonical5877 hH).trans (sound259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix862 (2 : Fin 4)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix862 (2 : Fin 4) = raw5953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix862 raw5953; decide +kernel
    rw [heq]
    exact (canonical5953 hH).trans (sound267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix862 (3 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix862 (3 : Fin 4) = raw5971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix862 raw5971; decide +kernel
    rw [heq]
    exact (canonical5971 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node862 + (injectiveMoment H (mergeFirst pivotMatrix862 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix862 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix862 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix862 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value862, value149, value259, value267, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation863 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix863 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound863 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node863 = Sparse.eval value863 (momentVector H) := by
  have heq : pivotMatrix863 = (fun u v => node863 (pivotPermutation863 u) v) := by apply Matrix.ext; unfold pivotMatrix863 node863 pivotPermutation863; decide +kernel
  have hmoment : injectiveMoment H node863 = injectiveMoment H pivotMatrix863 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix863 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix863 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix863 (0 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix863 (0 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix863 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix863 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix863 (1 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix863 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix863 (2 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix863 (2 : Fin 4) = raw5973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix863 raw5973; decide +kernel
    rw [heq]
    exact (canonical5973 hH).trans (sound268 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix863 (3 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix863 (3 : Fin 4) = raw5978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix863 raw5978; decide +kernel
    rw [heq]
    exact (canonical5978 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node863 + (injectiveMoment H (mergeFirst pivotMatrix863 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix863 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix863 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix863 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value863, value153, value261, value268, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation864 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix864 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound864 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node864 = Sparse.eval value864 (momentVector H) := by
  have heq : pivotMatrix864 = (fun u v => node864 (pivotPermutation864 u) v) := by apply Matrix.ext; unfold pivotMatrix864 node864 pivotPermutation864; decide +kernel
  have hmoment : injectiveMoment H node864 = injectiveMoment H pivotMatrix864 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix864 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix864 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix864 (0 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix864 (0 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix864 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix864 (1 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix864 (1 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix864 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix864 (2 : Fin 4)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix864 (2 : Fin 4) = raw5981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix864 raw5981; decide +kernel
    rw [heq]
    exact (canonical5981 hH).trans (sound269 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix864 (3 : Fin 4)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix864 (3 : Fin 4) = raw5983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix864 raw5983; decide +kernel
    rw [heq]
    exact (canonical5983 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node864 + (injectiveMoment H (mergeFirst pivotMatrix864 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix864 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix864 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix864 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value864, value155, value263, value269, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation865 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix865 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem sound865 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node865 = Sparse.eval value865 (momentVector H) := by
  have heq : pivotMatrix865 = (fun u v => node865 (pivotPermutation865 u) v) := by apply Matrix.ext; unfold pivotMatrix865 node865 pivotPermutation865; decide +kernel
  have hmoment : injectiveMoment H node865 = injectiveMoment H pivotMatrix865 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix865 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix865 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix865 (0 : Fin 4)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix865 (0 : Fin 4) = raw1441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix865 raw1441; decide +kernel
    rw [heq]
    exact (canonical1441 hH).trans (sound157 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix865 (1 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix865 (1 : Fin 4) = raw5908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix865 raw5908; decide +kernel
    rw [heq]
    exact (canonical5908 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix865 (2 : Fin 4)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix865 (2 : Fin 4) = raw5985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix865 raw5985; decide +kernel
    rw [heq]
    exact (canonical5985 hH).trans (sound270 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix865 (3 : Fin 4)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix865 (3 : Fin 4) = raw5987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix865 raw5987; decide +kernel
    rw [heq]
    exact (canonical5987 hH).trans (sound270 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node865 + (injectiveMoment H (mergeFirst pivotMatrix865 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix865 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix865 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix865 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value865, value157, value248, value270, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation866 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix866 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem sound866 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node866 = Sparse.eval value866 (momentVector H) := by
  have heq : pivotMatrix866 = (fun u v => node866 (pivotPermutation866 u) v) := by apply Matrix.ext; unfold pivotMatrix866 node866 pivotPermutation866; decide +kernel
  have hmoment : injectiveMoment H node866 = injectiveMoment H pivotMatrix866 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix866 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix866 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix866 (0 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix866 (0 : Fin 4) = raw2767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix866 raw2767; decide +kernel
    rw [heq]
    exact (canonical2767 hH).trans (sound175 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix866 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix866 (1 : Fin 4) = raw5872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix866 raw5872; decide +kernel
    rw [heq]
    exact (canonical5872 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix866 (2 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix866 (2 : Fin 4) = raw5937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix866 raw5937; decide +kernel
    rw [heq]
    exact (canonical5937 hH).trans (sound268 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix866 (3 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix866 (3 : Fin 4) = raw5943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix866 raw5943; decide +kernel
    rw [heq]
    exact (canonical5943 hH).trans (sound268 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node866 + (injectiveMoment H (mergeFirst pivotMatrix866 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix866 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix866 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix866 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value866, value175, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation867 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem sound867 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node867 = Sparse.eval value867 (momentVector H) := by
  have heq : pivotMatrix867 = (fun u v => node867 (pivotPermutation867 u) v) := by apply Matrix.ext; unfold pivotMatrix867 node867 pivotPermutation867; decide +kernel
  have hmoment : injectiveMoment H node867 = injectiveMoment H pivotMatrix867 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix867 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix867 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix867 (0 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix867 (0 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix867 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix867 (1 : Fin 4)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix867 (1 : Fin 4) = raw5887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix867 raw5887; decide +kernel
    rw [heq]
    exact (canonical5887 hH).trans (sound260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix867 (2 : Fin 4)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix867 (2 : Fin 4) = raw5953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix867 raw5953; decide +kernel
    rw [heq]
    exact (canonical5953 hH).trans (sound267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix867 (3 : Fin 4)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix867 (3 : Fin 4) = raw5970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix867 raw5970; decide +kernel
    rw [heq]
    exact (canonical5970 hH).trans (sound273 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node867 + (injectiveMoment H (mergeFirst pivotMatrix867 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix867 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix867 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix867 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value867, value180, value260, value267, value273, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation868 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound868 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node868 = Sparse.eval value868 (momentVector H) := by
  have heq : pivotMatrix868 = (fun u v => node868 (pivotPermutation868 u) v) := by apply Matrix.ext; unfold pivotMatrix868 node868 pivotPermutation868; decide +kernel
  have hmoment : injectiveMoment H node868 = injectiveMoment H pivotMatrix868 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix868 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix868 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix868 (0 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix868 (0 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix868 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix868 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix868 (1 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix868 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix868 (2 : Fin 4)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix868 (2 : Fin 4) = raw5956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix868 raw5956; decide +kernel
    rw [heq]
    exact (canonical5956 hH).trans (sound56 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix868 (3 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix868 (3 : Fin 4) = raw5971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix868 raw5971; decide +kernel
    rw [heq]
    exact (canonical5971 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node868 + (injectiveMoment H (mergeFirst pivotMatrix868 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix868 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix868 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix868 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value868, value181, value261, value272, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation869 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound869 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node869 = Sparse.eval value869 (momentVector H) := by
  have heq : pivotMatrix869 = (fun u v => node869 (pivotPermutation869 u) v) := by apply Matrix.ext; unfold pivotMatrix869 node869 pivotPermutation869; decide +kernel
  have hmoment : injectiveMoment H node869 = injectiveMoment H pivotMatrix869 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix869 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix869 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix869 (0 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix869 (0 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix869 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix869 (1 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix869 (1 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix869 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix869 (2 : Fin 4)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix869 (2 : Fin 4) = raw5974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix869 raw5974; decide +kernel
    rw [heq]
    exact (canonical5974 hH).trans (sound57 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix869 (3 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix869 (3 : Fin 4) = raw5978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix869 raw5978; decide +kernel
    rw [heq]
    exact (canonical5978 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node869 + (injectiveMoment H (mergeFirst pivotMatrix869 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix869 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix869 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix869 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value869, value185, value263, value272, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation870 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix870 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound870 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node870 = Sparse.eval value870 (momentVector H) := by
  have heq : pivotMatrix870 = (fun u v => node870 (pivotPermutation870 u) v) := by apply Matrix.ext; unfold pivotMatrix870 node870 pivotPermutation870; decide +kernel
  have hmoment : injectiveMoment H node870 = injectiveMoment H pivotMatrix870 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix870 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix870 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix870 (0 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix870 (0 : Fin 4) = raw5499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix870 raw5499; decide +kernel
    rw [heq]
    exact (canonical5499 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix870 (1 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix870 (1 : Fin 4) = raw5878 := by apply Matrix.ext; unfold mergeFirst pivotMatrix870 raw5878; decide +kernel
    rw [heq]
    exact (canonical5878 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix870 (2 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix870 (2 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix870 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix870 (3 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix870 (3 : Fin 4) = raw5889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix870 raw5889; decide +kernel
    rw [heq]
    exact (canonical5889 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node870 + (injectiveMoment H (mergeFirst pivotMatrix870 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix870 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix870 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix870 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value870, value176, value181, value246, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation871 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix871 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound871 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node871 = Sparse.eval value871 (momentVector H) := by
  have heq : pivotMatrix871 = (fun u v => node871 (pivotPermutation871 u) v) := by apply Matrix.ext; unfold pivotMatrix871 node871 pivotPermutation871; decide +kernel
  have hmoment : injectiveMoment H node871 = injectiveMoment H pivotMatrix871 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix871 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix871 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix871 (0 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix871 (0 : Fin 4) = raw6754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix871 raw6754; decide +kernel
    rw [heq]
    exact (canonical6754 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix871 (1 : Fin 4)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix871 (1 : Fin 4) = raw5899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix871 raw5899; decide +kernel
    rw [heq]
    exact (canonical5899 hH).trans (sound262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix871 (2 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix871 (2 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix871 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix871 (3 : Fin 4)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix871 (3 : Fin 4) = raw5887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix871 raw5887; decide +kernel
    rw [heq]
    exact (canonical5887 hH).trans (sound260 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node871 + (injectiveMoment H (mergeFirst pivotMatrix871 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix871 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix871 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix871 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value871, value260, value261, value262, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation872 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix872 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound872 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node872 = Sparse.eval value872 (momentVector H) := by
  have heq : pivotMatrix872 = (fun u v => node872 (pivotPermutation872 u) v) := by apply Matrix.ext; unfold pivotMatrix872 node872 pivotPermutation872; decide +kernel
  have hmoment : injectiveMoment H node872 = injectiveMoment H pivotMatrix872 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix872 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix872 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix872 (0 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix872 (0 : Fin 4) = raw6755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix872 raw6755; decide +kernel
    rw [heq]
    exact (canonical6755 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix872 (1 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix872 (1 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix872 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix872 (2 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix872 (2 : Fin 4) = raw5889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix872 raw5889; decide +kernel
    rw [heq]
    exact (canonical5889 hH).trans (sound176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix872 (3 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix872 (3 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix872 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node872 + (injectiveMoment H (mergeFirst pivotMatrix872 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix872 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix872 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix872 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value872, value176, value230, value261, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation873 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix873 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1]]

theorem sound873 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node873 = Sparse.eval value873 (momentVector H) := by
  have heq : pivotMatrix873 = (fun u v => node873 (pivotPermutation873 u) v) := by apply Matrix.ext; unfold pivotMatrix873 node873 pivotPermutation873; decide +kernel
  have hmoment : injectiveMoment H node873 = injectiveMoment H pivotMatrix873 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix873 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix873 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix873 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix873 (0 : Fin 4) = raw8166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix873 raw8166; decide +kernel
    rw [heq]
    exact (canonical8166 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix873 (1 : Fin 4)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix873 (1 : Fin 4) = raw5977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix873 raw5977; decide +kernel
    rw [heq]
    exact (canonical5977 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix873 (2 : Fin 4)) =
      Sparse.eval value260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix873 (2 : Fin 4) = raw5890 := by apply Matrix.ext; unfold mergeFirst pivotMatrix873 raw5890; decide +kernel
    rw [heq]
    exact (canonical5890 hH).trans (sound260 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix873 (3 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix873 (3 : Fin 4) = raw5886 := by apply Matrix.ext; unfold mergeFirst pivotMatrix873 raw5886; decide +kernel
    rw [heq]
    exact (canonical5886 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node873 + (injectiveMoment H (mergeFirst pivotMatrix873 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix873 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix873 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix873 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value873, value212, value260, value274, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation874 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix874 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2]]

theorem sound874 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node874 = Sparse.eval value874 (momentVector H) := by
  have heq : pivotMatrix874 = (fun u v => node874 (pivotPermutation874 u) v) := by apply Matrix.ext; unfold pivotMatrix874 node874 pivotPermutation874; decide +kernel
  have hmoment : injectiveMoment H node874 = injectiveMoment H pivotMatrix874 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix874 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix874 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix874 (0 : Fin 4)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix874 (0 : Fin 4) = raw8168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix874 raw8168; decide +kernel
    rw [heq]
    exact (canonical8168 hH).trans (sound274 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix874 (1 : Fin 4)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix874 (1 : Fin 4) = raw5980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix874 raw5980; decide +kernel
    rw [heq]
    exact (canonical5980 hH).trans (sound265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix874 (2 : Fin 4)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix874 (2 : Fin 4) = raw5899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix874 raw5899; decide +kernel
    rw [heq]
    exact (canonical5899 hH).trans (sound262 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix874 (3 : Fin 4)) =
      Sparse.eval value183 (momentVector H) := by
    have heq : mergeFirst pivotMatrix874 (3 : Fin 4) = raw5894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix874 raw5894; decide +kernel
    rw [heq]
    exact (canonical5894 hH).trans (sound183 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node874 + (injectiveMoment H (mergeFirst pivotMatrix874 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix874 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix874 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix874 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value874, value183, value262, value265, value274, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation875 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix875 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node875 = Sparse.eval value875 (momentVector H) := by
  have heq : pivotMatrix875 = (fun u v => node875 (pivotPermutation875 u) v) := by apply Matrix.ext; unfold pivotMatrix875 node875 pivotPermutation875; decide +kernel
  have hmoment : injectiveMoment H node875 = injectiveMoment H pivotMatrix875 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix875 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix875 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix875 (0 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix875 (0 : Fin 4) = raw5505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix875 raw5505; decide +kernel
    rw [heq]
    exact (canonical5505 hH).trans (sound247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix875 (1 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix875 (1 : Fin 4) = raw5888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix875 raw5888; decide +kernel
    rw [heq]
    exact (canonical5888 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix875 (2 : Fin 4)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix875 (2 : Fin 4) = raw5899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix875 raw5899; decide +kernel
    rw [heq]
    exact (canonical5899 hH).trans (sound262 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix875 (3 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix875 (3 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix875 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node875 + (injectiveMoment H (mergeFirst pivotMatrix875 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix875 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix875 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix875 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value875, value247, value261, value262, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation876 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix876 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound876 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node876 = Sparse.eval value876 (momentVector H) := by
  have heq : pivotMatrix876 = (fun u v => node876 (pivotPermutation876 u) v) := by apply Matrix.ext; unfold pivotMatrix876 node876 pivotPermutation876; decide +kernel
  have hmoment : injectiveMoment H node876 = injectiveMoment H pivotMatrix876 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix876 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix876 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix876 (0 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (0 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix876 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (1 : Fin 4) = raw5889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5889; decide +kernel
    rw [heq]
    exact (canonical5889 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix876 (2 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (2 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix876 (3 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (3 : Fin 4) = raw5901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5901; decide +kernel
    rw [heq]
    exact (canonical5901 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node876 + (injectiveMoment H (mergeFirst pivotMatrix876 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix876 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix876 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix876 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value876, value176, value248, value263, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation877 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix877 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -2, 3], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1]]

theorem sound877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node877 = Sparse.eval value877 (momentVector H) := by
  have heq : pivotMatrix877 = (fun u v => node877 (pivotPermutation877 u) v) := by apply Matrix.ext; unfold pivotMatrix877 node877 pivotPermutation877; decide +kernel
  have hmoment : injectiveMoment H node877 = injectiveMoment H pivotMatrix877 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix877 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix877 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix877 (0 : Fin 4)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (0 : Fin 4) = raw8170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw8170; decide +kernel
    rw [heq]
    exact (canonical8170 hH).trans (sound256 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix877 (1 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (1 : Fin 4) = raw5984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw5984; decide +kernel
    rw [heq]
    exact (canonical5984 hH).trans (sound266 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix877 (2 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (2 : Fin 4) = raw5907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw5907; decide +kernel
    rw [heq]
    exact (canonical5907 hH).trans (sound247 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix877 (3 : Fin 4)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (3 : Fin 4) = raw5904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw5904; decide +kernel
    rw [heq]
    exact (canonical5904 hH).trans (sound211 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node877 + (injectiveMoment H (mergeFirst pivotMatrix877 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix877 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix877 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix877 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value877, value211, value247, value256, value266, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation878 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix878 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3]]

theorem sound878 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node878 = Sparse.eval value878 (momentVector H) := by
  have heq : pivotMatrix878 = (fun u v => node878 (pivotPermutation878 u) v) := by apply Matrix.ext; unfold pivotMatrix878 node878 pivotPermutation878; decide +kernel
  have hmoment : injectiveMoment H node878 = injectiveMoment H pivotMatrix878 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix878 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix878 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix878 (0 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix878 (0 : Fin 4) = raw6779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix878 raw6779; decide +kernel
    rw [heq]
    exact (canonical6779 hH).trans (sound268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix878 (1 : Fin 4)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix878 (1 : Fin 4) = raw5933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix878 raw5933; decide +kernel
    rw [heq]
    exact (canonical5933 hH).trans (sound267 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix878 (2 : Fin 4)) =
      Sparse.eval value264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix878 (2 : Fin 4) = raw5913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix878 raw5913; decide +kernel
    rw [heq]
    exact (canonical5913 hH).trans (sound264 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix878 (3 : Fin 4)) =
      Sparse.eval value250 (momentVector H) := by
    have heq : mergeFirst pivotMatrix878 (3 : Fin 4) = raw5912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix878 raw5912; decide +kernel
    rw [heq]
    exact (canonical5912 hH).trans (sound250 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node878 + (injectiveMoment H (mergeFirst pivotMatrix878 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix878 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix878 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix878 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value878, value250, value264, value267, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation879 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix879 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem sound879 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node879 = Sparse.eval value879 (momentVector H) := by
  have heq : pivotMatrix879 = (fun u v => node879 (pivotPermutation879 u) v) := by apply Matrix.ext; unfold pivotMatrix879 node879 pivotPermutation879; decide +kernel
  have hmoment : injectiveMoment H node879 = injectiveMoment H pivotMatrix879 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix879 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix879 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix879 (0 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix879 (0 : Fin 4) = raw6786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix879 raw6786; decide +kernel
    rw [heq]
    exact (canonical6786 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix879 (1 : Fin 4)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix879 (1 : Fin 4) = raw5940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix879 raw5940; decide +kernel
    rw [heq]
    exact (canonical5940 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix879 (2 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix879 (2 : Fin 4) = raw5915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix879 raw5915; decide +kernel
    rw [heq]
    exact (canonical5915 hH).trans (sound266 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix879 (3 : Fin 4)) =
      Sparse.eval value265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix879 (3 : Fin 4) = raw5914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix879 raw5914; decide +kernel
    rw [heq]
    exact (canonical5914 hH).trans (sound265 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node879 + (injectiveMoment H (mergeFirst pivotMatrix879 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix879 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix879 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix879 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value879, value265, value266, value269, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation880 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix880 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem sound880 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node880 = Sparse.eval value880 (momentVector H) := by
  have heq : pivotMatrix880 = (fun u v => node880 (pivotPermutation880 u) v) := by apply Matrix.ext; unfold pivotMatrix880 node880 pivotPermutation880; decide +kernel
  have hmoment : injectiveMoment H node880 = injectiveMoment H pivotMatrix880 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix880 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix880 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix880 (0 : Fin 4)) =
      Sparse.eval value252 (momentVector H) := by
    have heq : mergeFirst pivotMatrix880 (0 : Fin 4) = raw5515 := by apply Matrix.ext; unfold mergeFirst pivotMatrix880 raw5515; decide +kernel
    rw [heq]
    exact (canonical5515 hH).trans (sound252 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix880 (1 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix880 (1 : Fin 4) = raw5915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix880 raw5915; decide +kernel
    rw [heq]
    exact (canonical5915 hH).trans (sound266 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix880 (2 : Fin 4)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix880 (2 : Fin 4) = raw5940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix880 raw5940; decide +kernel
    rw [heq]
    exact (canonical5940 hH).trans (sound269 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix880 (3 : Fin 4)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix880 (3 : Fin 4) = raw5942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix880 raw5942; decide +kernel
    rw [heq]
    exact (canonical5942 hH).trans (sound270 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node880 + (injectiveMoment H (mergeFirst pivotMatrix880 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix880 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix880 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix880 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value880, value252, value266, value269, value270, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation881 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix881 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem sound881 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node881 = Sparse.eval value881 (momentVector H) := by
  have heq : pivotMatrix881 = (fun u v => node881 (pivotPermutation881 u) v) := by apply Matrix.ext; unfold pivotMatrix881 node881 pivotPermutation881; decide +kernel
  have hmoment : injectiveMoment H node881 = injectiveMoment H pivotMatrix881 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix881 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix881 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix881 (0 : Fin 4)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix881 (0 : Fin 4) = raw5530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix881 raw5530; decide +kernel
    rw [heq]
    exact (canonical5530 hH).trans (sound253 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix881 (1 : Fin 4)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix881 (1 : Fin 4) = raw5946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix881 raw5946; decide +kernel
    rw [heq]
    exact (canonical5946 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix881 (2 : Fin 4)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix881 (2 : Fin 4) = raw5956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix881 raw5956; decide +kernel
    rw [heq]
    exact (canonical5956 hH).trans (sound56 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix881 (3 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix881 (3 : Fin 4) = raw5962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix881 raw5962; decide +kernel
    rw [heq]
    exact (canonical5962 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node881 + (injectiveMoment H (mergeFirst pivotMatrix881 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix881 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix881 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix881 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value881, value253, value271, value56, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation882 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix882 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem sound882 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node882 = Sparse.eval value882 (momentVector H) := by
  have heq : pivotMatrix882 = (fun u v => node882 (pivotPermutation882 u) v) := by apply Matrix.ext; unfold pivotMatrix882 node882 pivotPermutation882; decide +kernel
  have hmoment : injectiveMoment H node882 = injectiveMoment H pivotMatrix882 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix882 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix882 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix882 (0 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix882 (0 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix882 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix882 (1 : Fin 4)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix882 (1 : Fin 4) = raw5947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix882 raw5947; decide +kernel
    rw [heq]
    exact (canonical5947 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix882 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix882 (2 : Fin 4) = raw5962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix882 raw5962; decide +kernel
    rw [heq]
    exact (canonical5962 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix882 (3 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix882 (3 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix882 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node882 + (injectiveMoment H (mergeFirst pivotMatrix882 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix882 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix882 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix882 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value882, value254, value271, value272, value57, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation883 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix883 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem sound883 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node883 = Sparse.eval value883 (momentVector H) := by
  have heq : pivotMatrix883 = (fun u v => node883 (pivotPermutation883 u) v) := by apply Matrix.ext; unfold pivotMatrix883 node883 pivotPermutation883; decide +kernel
  have hmoment : injectiveMoment H node883 = injectiveMoment H pivotMatrix883 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix883 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix883 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix883 (0 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix883 (0 : Fin 4) = raw5536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix883 raw5536; decide +kernel
    rw [heq]
    exact (canonical5536 hH).trans (sound255 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix883 (1 : Fin 4)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix883 (1 : Fin 4) = raw5948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix883 raw5948; decide +kernel
    rw [heq]
    exact (canonical5948 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix883 (2 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix883 (2 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix883 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix883 (3 : Fin 4)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix883 (3 : Fin 4) = raw5968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix883 raw5968; decide +kernel
    rw [heq]
    exact (canonical5968 hH).trans (sound273 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node883 + (injectiveMoment H (mergeFirst pivotMatrix883 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix883 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix883 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix883 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value883, value255, value272, value273, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation884 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix884 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem sound884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node884 = Sparse.eval value884 (momentVector H) := by
  have heq : pivotMatrix884 = (fun u v => node884 (pivotPermutation884 u) v) := by apply Matrix.ext; unfold pivotMatrix884 node884 pivotPermutation884; decide +kernel
  have hmoment : injectiveMoment H node884 = injectiveMoment H pivotMatrix884 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix884 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix884 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix884 (0 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix884 (0 : Fin 4) = raw6845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix884 raw6845; decide +kernel
    rw [heq]
    exact (canonical6845 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix884 (1 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix884 (1 : Fin 4) = raw5976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix884 raw5976; decide +kernel
    rw [heq]
    exact (canonical5976 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix884 (2 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix884 (2 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix884 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix884 (3 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix884 (3 : Fin 4) = raw5962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix884 raw5962; decide +kernel
    rw [heq]
    exact (canonical5962 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node884 + (injectiveMoment H (mergeFirst pivotMatrix884 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix884 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix884 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix884 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value884, value271, value272, value287, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation885 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix885 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem sound885 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node885 = Sparse.eval value885 (momentVector H) := by
  have heq : pivotMatrix885 = (fun u v => node885 (pivotPermutation885 u) v) := by apply Matrix.ext; unfold pivotMatrix885 node885 pivotPermutation885; decide +kernel
  have hmoment : injectiveMoment H node885 = injectiveMoment H pivotMatrix885 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix885 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix885 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix885 (0 : Fin 4)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix885 (0 : Fin 4) = raw6852 := by apply Matrix.ext; unfold mergeFirst pivotMatrix885 raw6852; decide +kernel
    rw [heq]
    exact (canonical6852 hH).trans (sound288 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix885 (1 : Fin 4)) =
      Sparse.eval value274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix885 (1 : Fin 4) = raw5977 := by apply Matrix.ext; unfold mergeFirst pivotMatrix885 raw5977; decide +kernel
    rw [heq]
    exact (canonical5977 hH).trans (sound274 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix885 (2 : Fin 4)) =
      Sparse.eval value273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix885 (2 : Fin 4) = raw5968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix885 raw5968; decide +kernel
    rw [heq]
    exact (canonical5968 hH).trans (sound273 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix885 (3 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix885 (3 : Fin 4) = raw5965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix885 raw5965; decide +kernel
    rw [heq]
    exact (canonical5965 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node885 + (injectiveMoment H (mergeFirst pivotMatrix885 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix885 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix885 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix885 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value885, value272, value273, value274, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation886 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix886 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-3, 2, 1, 0], ![5, -1, -2, -2]]

theorem sound886 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node886 = Sparse.eval value886 (momentVector H) := by
  have heq : pivotMatrix886 = (fun u v => node886.transpose (pivotPermutation886 u) v) := by apply Matrix.ext; unfold pivotMatrix886 node886 pivotPermutation886; decide +kernel
  have hmoment : injectiveMoment H node886 = injectiveMoment H pivotMatrix886 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix886 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix886 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix886 (0 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix886 (0 : Fin 3) = raw2133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix886 raw2133; decide +kernel
    rw [heq]
    exact (canonical2133 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix886 (1 : Fin 3)) =
      Sparse.eval value234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix886 (1 : Fin 3) = raw6569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix886 raw6569; decide +kernel
    rw [heq]
    exact (canonical6569 hH).trans (sound234 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix886 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix886 (2 : Fin 3) = raw6570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix886 raw6570; decide +kernel
    rw [heq]
    exact (canonical6570 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node886 + (injectiveMoment H (mergeFirst pivotMatrix886 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix886 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix886 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value886, value234, value246, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation887 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix887 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-3, 2, 0, 1], ![5, -1, -2, -2]]

theorem sound887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node887 = Sparse.eval value887 (momentVector H) := by
  have heq : pivotMatrix887 = (fun u v => node887.transpose (pivotPermutation887 u) v) := by apply Matrix.ext; unfold pivotMatrix887 node887 pivotPermutation887; decide +kernel
  have hmoment : injectiveMoment H node887 = injectiveMoment H pivotMatrix887 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix887 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix887 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix887 (0 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix887 (0 : Fin 3) = raw2522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix887 raw2522; decide +kernel
    rw [heq]
    exact (canonical2522 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix887 (1 : Fin 3)) =
      Sparse.eval value200 (momentVector H) := by
    have heq : mergeFirst pivotMatrix887 (1 : Fin 3) = raw6887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix887 raw6887; decide +kernel
    rw [heq]
    exact (canonical6887 hH).trans (sound200 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix887 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix887 (2 : Fin 3) = raw6890 := by apply Matrix.ext; unfold mergeFirst pivotMatrix887 raw6890; decide +kernel
    rw [heq]
    exact (canonical6890 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node887 + (injectiveMoment H (mergeFirst pivotMatrix887 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix887 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix887 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value887, value200, value206, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation888 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix888 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -3, 5], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem sound888 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node888 = Sparse.eval value888 (momentVector H) := by
  have heq : pivotMatrix888 = (fun u v => node888 (pivotPermutation888 u) v) := by apply Matrix.ext; unfold pivotMatrix888 node888 pivotPermutation888; decide +kernel
  have hmoment : injectiveMoment H node888 = injectiveMoment H pivotMatrix888 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix888 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix888 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix888 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix888 (0 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix888 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix888 (1 : Fin 3)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix888 (1 : Fin 3) = raw6000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix888 raw6000; decide +kernel
    rw [heq]
    exact (canonical6000 hH).trans (sound129 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix888 (2 : Fin 3)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix888 (2 : Fin 3) = raw5999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix888 raw5999; decide +kernel
    rw [heq]
    exact (canonical5999 hH).trans (sound119 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node888 + (injectiveMoment H (mergeFirst pivotMatrix888 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix888 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix888 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value888, value119, value129, value145, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation889 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix889 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -1, -3, 5], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node889 = Sparse.eval value889 (momentVector H) := by
  have heq : pivotMatrix889 = (fun u v => node889 (pivotPermutation889 u) v) := by apply Matrix.ext; unfold pivotMatrix889 node889 pivotPermutation889; decide +kernel
  have hmoment : injectiveMoment H node889 = injectiveMoment H pivotMatrix889 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix889 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix889 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix889 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix889 (0 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix889 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix889 (1 : Fin 3)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix889 (1 : Fin 3) = raw6002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix889 raw6002; decide +kernel
    rw [heq]
    exact (canonical6002 hH).trans (sound123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix889 (2 : Fin 3)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix889 (2 : Fin 3) = raw6001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix889 raw6001; decide +kernel
    rw [heq]
    exact (canonical6001 hH).trans (sound123 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node889 + (injectiveMoment H (mergeFirst pivotMatrix889 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix889 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix889 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value889, value123, value150, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation890 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix890 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -1, -3, 5], ![0, 0, 2, -2], ![1, 0, 1, -2]]

theorem sound890 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node890 = Sparse.eval value890 (momentVector H) := by
  have heq : pivotMatrix890 = (fun u v => node890 (pivotPermutation890 u) v) := by apply Matrix.ext; unfold pivotMatrix890 node890 pivotPermutation890; decide +kernel
  have hmoment : injectiveMoment H node890 = injectiveMoment H pivotMatrix890 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix890 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix890 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix890 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix890 (0 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix890 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix890 (1 : Fin 3)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix890 (1 : Fin 3) = raw6002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix890 raw6002; decide +kernel
    rw [heq]
    exact (canonical6002 hH).trans (sound123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix890 (2 : Fin 3)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix890 (2 : Fin 3) = raw5999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix890 raw5999; decide +kernel
    rw [heq]
    exact (canonical5999 hH).trans (sound119 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node890 + (injectiveMoment H (mergeFirst pivotMatrix890 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix890 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix890 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value890, value119, value123, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node891 = Sparse.eval value891 (momentVector H) := by
  have hc : momentVector H 855 = injectiveMoment H node891 := rfl
  simp [value891, Sparse.eval, hc]

def pivotPermutation892 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix892 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, -2, 4], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem sound892 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node892 = Sparse.eval value892 (momentVector H) := by
  have heq : pivotMatrix892 = (fun u v => node892 (pivotPermutation892 u) v) := by apply Matrix.ext; unfold pivotMatrix892 node892 pivotPermutation892; decide +kernel
  have hmoment : injectiveMoment H node892 = injectiveMoment H pivotMatrix892 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix892 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix892 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix892 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix892 (0 : Fin 3) = raw5636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix892 raw5636; decide +kernel
    rw [heq]
    exact (canonical5636 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix892 (1 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix892 (1 : Fin 3) = raw6105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix892 raw6105; decide +kernel
    rw [heq]
    exact (canonical6105 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix892 (2 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix892 (2 : Fin 3) = raw6112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix892 raw6112; decide +kernel
    rw [heq]
    exact (canonical6112 hH).trans (sound228 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node892 + (injectiveMoment H (mergeFirst pivotMatrix892 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix892 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix892 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value892, value206, value228, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation893 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix893 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -1, -2, 4], ![0, -1, 2, -1], ![1, 1, 1, -3]]

theorem sound893 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node893 = Sparse.eval value893 (momentVector H) := by
  have heq : pivotMatrix893 = (fun u v => node893 (pivotPermutation893 u) v) := by apply Matrix.ext; unfold pivotMatrix893 node893 pivotPermutation893; decide +kernel
  have hmoment : injectiveMoment H node893 = injectiveMoment H pivotMatrix893 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix893 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix893 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix893 (0 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix893 (0 : Fin 3) = raw7001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix893 raw7001; decide +kernel
    rw [heq]
    exact (canonical7001 hH).trans (sound173 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix893 (1 : Fin 3)) =
      Sparse.eval value253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix893 (1 : Fin 3) = raw6083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix893 raw6083; decide +kernel
    rw [heq]
    exact (canonical6083 hH).trans (sound253 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix893 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix893 (2 : Fin 3) = raw6046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix893 raw6046; decide +kernel
    rw [heq]
    exact (canonical6046 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node893 + (injectiveMoment H (mergeFirst pivotMatrix893 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix893 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix893 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value893, value173, value206, value253, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation894 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix894 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 1, 1], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

theorem sound894 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node894 = Sparse.eval value894 (momentVector H) := by
  have heq : pivotMatrix894 = (fun u v => node894.transpose (pivotPermutation894 u) v) := by apply Matrix.ext; unfold pivotMatrix894 node894 pivotPermutation894; decide +kernel
  have hmoment : injectiveMoment H node894 = injectiveMoment H pivotMatrix894 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix894 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix894 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix894 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix894 (0 : Fin 3) = raw2134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix894 raw2134; decide +kernel
    rw [heq]
    exact (canonical2134 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix894 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix894 (1 : Fin 3) = raw6570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix894 raw6570; decide +kernel
    rw [heq]
    exact (canonical6570 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix894 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix894 (2 : Fin 3) = raw6575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix894 raw6575; decide +kernel
    rw [heq]
    exact (canonical6575 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node894 + (injectiveMoment H (mergeFirst pivotMatrix894 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix894 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix894 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value894, value134, value246, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation895 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix895 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-2, 2, -2, 2], ![4, -1, 0, -3]]

theorem sound895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node895 = Sparse.eval value895 (momentVector H) := by
  have heq : pivotMatrix895 = (fun u v => node895.transpose (pivotPermutation895 u) v) := by apply Matrix.ext; unfold pivotMatrix895 node895 pivotPermutation895; decide +kernel
  have hmoment : injectiveMoment H node895 = injectiveMoment H pivotMatrix895 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix895 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix895 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix895 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix895 (0 : Fin 3) = raw2523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix895 raw2523; decide +kernel
    rw [heq]
    exact (canonical2523 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix895 (1 : Fin 3)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix895 (1 : Fin 3) = raw6888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix895 raw6888; decide +kernel
    rw [heq]
    exact (canonical6888 hH).trans (sound213 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix895 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix895 (2 : Fin 3) = raw6894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix895 raw6894; decide +kernel
    rw [heq]
    exact (canonical6894 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node895 + (injectiveMoment H (mergeFirst pivotMatrix895 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix895 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix895 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value895, value135, value212, value213, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
