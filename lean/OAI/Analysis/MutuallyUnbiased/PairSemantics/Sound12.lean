import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical207
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical253

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation768 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix768 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem sound768 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node768 = Sparse.eval value768 (momentVector H) := by
  have heq : pivotMatrix768 = (fun u v => node768 (pivotPermutation768 u) v) := by apply Matrix.ext; unfold pivotMatrix768 node768 pivotPermutation768; decide +kernel
  have hmoment : injectiveMoment H node768 = injectiveMoment H pivotMatrix768 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix768 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix768 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix768 (0 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix768 (0 : Fin 3) = raw5724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix768 raw5724; decide +kernel
    rw [heq]
    exact (canonical5724 hH).trans (sound204 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix768 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix768 (1 : Fin 3) = raw5636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix768 raw5636; decide +kernel
    rw [heq]
    exact (canonical5636 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix768 (2 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix768 (2 : Fin 3) = raw5635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix768 raw5635; decide +kernel
    rw [heq]
    exact (canonical5635 hH).trans (sound171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node768 + (injectiveMoment H (mergeFirst pivotMatrix768 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix768 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix768 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value768, value171, value204, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation769 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix769 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, -1, 4], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound769 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node769 = Sparse.eval value769 (momentVector H) := by
  have heq : pivotMatrix769 = (fun u v => node769 (pivotPermutation769 u) v) := by apply Matrix.ext; unfold pivotMatrix769 node769 pivotPermutation769; decide +kernel
  have hmoment : injectiveMoment H node769 = injectiveMoment H pivotMatrix769 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix769 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix769 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix769 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix769 (0 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix769 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix769 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix769 (1 : Fin 3) = raw5637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix769 raw5637; decide +kernel
    rw [heq]
    exact (canonical5637 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix769 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix769 (2 : Fin 3) = raw5636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix769 raw5636; decide +kernel
    rw [heq]
    exact (canonical5636 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node769 + (injectiveMoment H (mergeFirst pivotMatrix769 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix769 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix769 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value769, value145, value185, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation770 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix770 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 2, -2, 1], ![4, -2, 1, -3]]

theorem sound770 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node770 = Sparse.eval value770 (momentVector H) := by
  have heq : pivotMatrix770 = (fun u v => node770.transpose (pivotPermutation770 u) v) := by apply Matrix.ext; unfold pivotMatrix770 node770 pivotPermutation770; decide +kernel
  have hmoment : injectiveMoment H node770 = injectiveMoment H pivotMatrix770 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix770 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix770 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix770 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix770 (0 : Fin 3) = raw340 := by apply Matrix.ext; unfold mergeFirst pivotMatrix770 raw340; decide +kernel
    rw [heq]
    exact (canonical340 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix770 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix770 (1 : Fin 3) = raw3645 := by apply Matrix.ext; unfold mergeFirst pivotMatrix770 raw3645; decide +kernel
    rw [heq]
    exact (canonical3645 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix770 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix770 (2 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix770 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node770 + (injectiveMoment H (mergeFirst pivotMatrix770 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix770 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix770 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value770, value152, value184, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation771 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix771 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem sound771 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node771 = Sparse.eval value771 (momentVector H) := by
  have heq : pivotMatrix771 = (fun u v => node771 (pivotPermutation771 u) v) := by apply Matrix.ext; unfold pivotMatrix771 node771 pivotPermutation771; decide +kernel
  have hmoment : injectiveMoment H node771 = injectiveMoment H pivotMatrix771 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix771 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix771 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix771 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (0 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix771 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (1 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix771 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node771 + (injectiveMoment H (mergeFirst pivotMatrix771 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix771 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix771 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value771, value145, value146, value150, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation772 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 2, 1, -2], ![4, -2, -2, 0]]

theorem sound772 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node772 = Sparse.eval value772 (momentVector H) := by
  have heq : pivotMatrix772 = (fun u v => node772.transpose (pivotPermutation772 u) v) := by apply Matrix.ext; unfold pivotMatrix772 node772 pivotPermutation772; decide +kernel
  have hmoment : injectiveMoment H node772 = injectiveMoment H pivotMatrix772 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix772 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix772 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix772 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix772 (0 : Fin 3) = raw341 := by apply Matrix.ext; unfold mergeFirst pivotMatrix772 raw341; decide +kernel
    rw [heq]
    exact (canonical341 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix772 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix772 (1 : Fin 3) = raw3646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix772 raw3646; decide +kernel
    rw [heq]
    exact (canonical3646 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix772 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix772 (2 : Fin 3) = raw3652 := by apply Matrix.ext; unfold mergeFirst pivotMatrix772 raw3652; decide +kernel
    rw [heq]
    exact (canonical3652 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node772 + (injectiveMoment H (mergeFirst pivotMatrix772 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix772 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix772 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value772, value153, value184, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation773 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 2, -2, 1], ![4, -2, 0, -2]]

theorem sound773 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node773 = Sparse.eval value773 (momentVector H) := by
  have heq : pivotMatrix773 = (fun u v => node773.transpose (pivotPermutation773 u) v) := by apply Matrix.ext; unfold pivotMatrix773 node773 pivotPermutation773; decide +kernel
  have hmoment : injectiveMoment H node773 = injectiveMoment H pivotMatrix773 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix773 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix773 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix773 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix773 (0 : Fin 3) = raw356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix773 raw356; decide +kernel
    rw [heq]
    exact (canonical356 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix773 (1 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix773 (1 : Fin 3) = raw4165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix773 raw4165; decide +kernel
    rw [heq]
    exact (canonical4165 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix773 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix773 (2 : Fin 3) = raw4171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix773 raw4171; decide +kernel
    rw [heq]
    exact (canonical4171 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node773 + (injectiveMoment H (mergeFirst pivotMatrix773 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix773 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix773 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value773, value151, value177, value85, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation774 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix774 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1]]

theorem sound774 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node774 = Sparse.eval value774 (momentVector H) := by
  have heq : pivotMatrix774 = (fun u v => node774 (pivotPermutation774 u) v) := by apply Matrix.ext; unfold pivotMatrix774 node774 pivotPermutation774; decide +kernel
  have hmoment : injectiveMoment H node774 = injectiveMoment H pivotMatrix774 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix774 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix774 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix774 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix774 (0 : Fin 3) = raw8046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix774 raw8046; decide +kernel
    rw [heq]
    exact (canonical8046 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix774 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix774 (1 : Fin 3) = raw5640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix774 raw5640; decide +kernel
    rw [heq]
    exact (canonical5640 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix774 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix774 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix774 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node774 + (injectiveMoment H (mergeFirst pivotMatrix774 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix774 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix774 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value774, value146, value206, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation775 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix775 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

theorem sound775 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node775 = Sparse.eval value775 (momentVector H) := by
  have heq : pivotMatrix775 = (fun u v => node775 (pivotPermutation775 u) v) := by apply Matrix.ext; unfold pivotMatrix775 node775 pivotPermutation775; decide +kernel
  have hmoment : injectiveMoment H node775 = injectiveMoment H pivotMatrix775 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix775 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix775 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix775 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (0 : Fin 3) = raw8021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw8021; decide +kernel
    rw [heq]
    exact (canonical8021 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix775 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (1 : Fin 3) = raw5639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw5639; decide +kernel
    rw [heq]
    exact (canonical5639 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix775 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node775 + (injectiveMoment H (mergeFirst pivotMatrix775 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix775 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix775 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value775, value145, value146, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation776 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix776 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 2, 1, -2], ![4, -2, -3, 1]]

theorem sound776 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node776 = Sparse.eval value776 (momentVector H) := by
  have heq : pivotMatrix776 = (fun u v => node776.transpose (pivotPermutation776 u) v) := by apply Matrix.ext; unfold pivotMatrix776 node776 pivotPermutation776; decide +kernel
  have hmoment : injectiveMoment H node776 = injectiveMoment H pivotMatrix776 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix776 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix776 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix776 (0 : Fin 3)) =
      Sparse.eval value84 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (0 : Fin 3) = raw357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw357; decide +kernel
    rw [heq]
    exact (canonical357 hH).trans (sound84 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix776 (1 : Fin 3)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (1 : Fin 3) = raw4167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw4167; decide +kernel
    rw [heq]
    exact (canonical4167 hH).trans (sound140 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix776 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix776 (2 : Fin 3) = raw4173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix776 raw4173; decide +kernel
    rw [heq]
    exact (canonical4173 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node776 + (injectiveMoment H (mergeFirst pivotMatrix776 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix776 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix776 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value776, value140, value162, value84, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation777 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 3, -1], ![-1, 2, -2, 1], ![4, -2, -1, -1]]

theorem sound777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node777 = Sparse.eval value777 (momentVector H) := by
  have heq : pivotMatrix777 = (fun u v => node777.transpose (pivotPermutation777 u) v) := by apply Matrix.ext; unfold pivotMatrix777 node777 pivotPermutation777; decide +kernel
  have hmoment : injectiveMoment H node777 = injectiveMoment H pivotMatrix777 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix777 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix777 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix777 (0 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix777 (0 : Fin 3) = raw584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix777 raw584; decide +kernel
    rw [heq]
    exact (canonical584 hH).trans (sound81 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix777 (1 : Fin 3)) =
      Sparse.eval value112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix777 (1 : Fin 3) = raw4212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix777 raw4212; decide +kernel
    rw [heq]
    exact (canonical4212 hH).trans (sound112 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix777 (2 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix777 (2 : Fin 3) = raw4213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix777 raw4213; decide +kernel
    rw [heq]
    exact (canonical4213 hH).trans (sound107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node777 + (injectiveMoment H (mergeFirst pivotMatrix777 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix777 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix777 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value777, value107, value112, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation778 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 3, -2, 0], ![4, -3, 1, -2]]

theorem sound778 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node778 = Sparse.eval value778 (momentVector H) := by
  have heq : pivotMatrix778 = (fun u v => node778.transpose (pivotPermutation778 u) v) := by apply Matrix.ext; unfold pivotMatrix778 node778 pivotPermutation778; decide +kernel
  have hmoment : injectiveMoment H node778 = injectiveMoment H pivotMatrix778 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix778 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix778 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix778 (0 : Fin 3)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix778 (0 : Fin 3) = raw342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix778 raw342; decide +kernel
    rw [heq]
    exact (canonical342 hH).trans (sound86 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix778 (1 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix778 (1 : Fin 3) = raw3647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix778 raw3647; decide +kernel
    rw [heq]
    exact (canonical3647 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix778 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix778 (2 : Fin 3) = raw3653 := by apply Matrix.ext; unfold mergeFirst pivotMatrix778 raw3653; decide +kernel
    rw [heq]
    exact (canonical3653 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node778 + (injectiveMoment H (mergeFirst pivotMatrix778 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix778 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix778 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value778, value154, value187, value86, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation779 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix779 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem sound779 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node779 = Sparse.eval value779 (momentVector H) := by
  have heq : pivotMatrix779 = (fun u v => node779 (pivotPermutation779 u) v) := by apply Matrix.ext; unfold pivotMatrix779 node779 pivotPermutation779; decide +kernel
  have hmoment : injectiveMoment H node779 = injectiveMoment H pivotMatrix779 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix779 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix779 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix779 (0 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix779 (0 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix779 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix779 (1 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix779 (1 : Fin 3) = raw5633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix779 raw5633; decide +kernel
    rw [heq]
    exact (canonical5633 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix779 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix779 (2 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix779 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node779 + (injectiveMoment H (mergeFirst pivotMatrix779 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix779 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix779 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value779, value246, value248, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation780 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix780 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem sound780 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node780 = Sparse.eval value780 (momentVector H) := by
  have heq : pivotMatrix780 = (fun u v => node780 (pivotPermutation780 u) v) := by apply Matrix.ext; unfold pivotMatrix780 node780 pivotPermutation780; decide +kernel
  have hmoment : injectiveMoment H node780 = injectiveMoment H pivotMatrix780 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix780 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix780 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix780 (0 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix780 (0 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix780 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix780 (1 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix780 (1 : Fin 3) = raw5634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix780 raw5634; decide +kernel
    rw [heq]
    exact (canonical5634 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix780 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix780 (2 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix780 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node780 + (injectiveMoment H (mergeFirst pivotMatrix780 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix780 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix780 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value780, value188, value190, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation781 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix781 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0]]

theorem sound781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node781 = Sparse.eval value781 (momentVector H) := by
  have heq : pivotMatrix781 = (fun u v => node781 (pivotPermutation781 u) v) := by apply Matrix.ext; unfold pivotMatrix781 node781 pivotPermutation781; decide +kernel
  have hmoment : injectiveMoment H node781 = injectiveMoment H pivotMatrix781 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix781 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix781 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix781 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix781 (0 : Fin 3) = raw8047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix781 raw8047; decide +kernel
    rw [heq]
    exact (canonical8047 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix781 (1 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix781 (1 : Fin 3) = raw5641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix781 raw5641; decide +kernel
    rw [heq]
    exact (canonical5641 hH).trans (sound171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix781 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix781 (2 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix781 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node781 + (injectiveMoment H (mergeFirst pivotMatrix781 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix781 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix781 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value781, value171, value37, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation782 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix782 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

theorem sound782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node782 = Sparse.eval value782 (momentVector H) := by
  have heq : pivotMatrix782 = (fun u v => node782 (pivotPermutation782 u) v) := by apply Matrix.ext; unfold pivotMatrix782 node782 pivotPermutation782; decide +kernel
  have hmoment : injectiveMoment H node782 = injectiveMoment H pivotMatrix782 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix782 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix782 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix782 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix782 (0 : Fin 3) = raw8023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix782 raw8023; decide +kernel
    rw [heq]
    exact (canonical8023 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix782 (1 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix782 (1 : Fin 3) = raw5640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix782 raw5640; decide +kernel
    rw [heq]
    exact (canonical5640 hH).trans (sound206 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix782 (2 : Fin 3)) =
      Sparse.eval value81 (momentVector H) := by
    have heq : mergeFirst pivotMatrix782 (2 : Fin 3) = raw5619 := by apply Matrix.ext; unfold mergeFirst pivotMatrix782 raw5619; decide +kernel
    rw [heq]
    exact (canonical5619 hH).trans (sound81 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node782 + (injectiveMoment H (mergeFirst pivotMatrix782 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix782 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix782 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value782, value206, value32, value81, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation783 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix783 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![-1, 3, 0, -2], ![4, -3, -2, 1]]

theorem sound783 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node783 = Sparse.eval value783 (momentVector H) := by
  have heq : pivotMatrix783 = (fun u v => node783.transpose (pivotPermutation783 u) v) := by apply Matrix.ext; unfold pivotMatrix783 node783 pivotPermutation783; decide +kernel
  have hmoment : injectiveMoment H node783 = injectiveMoment H pivotMatrix783 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix783 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix783 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix783 (0 : Fin 3)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix783 (0 : Fin 3) = raw358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix783 raw358; decide +kernel
    rw [heq]
    exact (canonical358 hH).trans (sound86 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix783 (1 : Fin 3)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix783 (1 : Fin 3) = raw4168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix783 raw4168; decide +kernel
    rw [heq]
    exact (canonical4168 hH).trans (sound141 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix783 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix783 (2 : Fin 3) = raw4175 := by apply Matrix.ext; unfold mergeFirst pivotMatrix783 raw4175; decide +kernel
    rw [heq]
    exact (canonical4175 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node783 + (injectiveMoment H (mergeFirst pivotMatrix783 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix783 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix783 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value783, value141, value163, value86, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation784 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -2, 1, 2], ![4, 1, -2, -3]]

theorem sound784 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node784 = Sparse.eval value784 (momentVector H) := by
  have heq : pivotMatrix784 = (fun u v => node784.transpose (pivotPermutation784 u) v) := by apply Matrix.ext; unfold pivotMatrix784 node784 pivotPermutation784; decide +kernel
  have hmoment : injectiveMoment H node784 = injectiveMoment H pivotMatrix784 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix784 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix784 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix784 (0 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix784 (0 : Fin 3) = raw589 := by apply Matrix.ext; unfold mergeFirst pivotMatrix784 raw589; decide +kernel
    rw [heq]
    exact (canonical589 hH).trans (sound89 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix784 (1 : Fin 3)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix784 (1 : Fin 3) = raw4968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix784 raw4968; decide +kernel
    rw [heq]
    exact (canonical4968 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix784 (2 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix784 (2 : Fin 3) = raw4971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix784 raw4971; decide +kernel
    rw [heq]
    exact (canonical4971 hH).trans (sound184 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node784 + (injectiveMoment H (mergeFirst pivotMatrix784 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix784 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix784 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value784, value154, value184, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation785 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix785 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, -2, 2, 1], ![4, 1, -3, -2]]

theorem sound785 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node785 = Sparse.eval value785 (momentVector H) := by
  have heq : pivotMatrix785 = (fun u v => node785.transpose (pivotPermutation785 u) v) := by apply Matrix.ext; unfold pivotMatrix785 node785 pivotPermutation785; decide +kernel
  have hmoment : injectiveMoment H node785 = injectiveMoment H pivotMatrix785 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix785 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix785 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix785 (0 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix785 (0 : Fin 3) = raw590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix785 raw590; decide +kernel
    rw [heq]
    exact (canonical590 hH).trans (sound89 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix785 (1 : Fin 3)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix785 (1 : Fin 3) = raw4969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix785 raw4969; decide +kernel
    rw [heq]
    exact (canonical4969 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix785 (2 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix785 (2 : Fin 3) = raw4972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix785 raw4972; decide +kernel
    rw [heq]
    exact (canonical4972 hH).trans (sound180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node785 + (injectiveMoment H (mergeFirst pivotMatrix785 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix785 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix785 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value785, value152, value180, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation786 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix786 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound786 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node786 = Sparse.eval value786 (momentVector H) := by
  have heq : pivotMatrix786 = (fun u v => node786 (pivotPermutation786 u) v) := by apply Matrix.ext; unfold pivotMatrix786 node786 pivotPermutation786; decide +kernel
  have hmoment : injectiveMoment H node786 = injectiveMoment H pivotMatrix786 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix786 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix786 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix786 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix786 (0 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix786 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix786 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix786 (1 : Fin 3) = raw5637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix786 raw5637; decide +kernel
    rw [heq]
    exact (canonical5637 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix786 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix786 (2 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix786 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node786 + (injectiveMoment H (mergeFirst pivotMatrix786 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix786 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix786 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value786, value145, value150, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation787 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix787 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2]]

theorem sound787 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node787 = Sparse.eval value787 (momentVector H) := by
  have heq : pivotMatrix787 = (fun u v => node787 (pivotPermutation787 u) v) := by apply Matrix.ext; unfold pivotMatrix787 node787 pivotPermutation787; decide +kernel
  have hmoment : injectiveMoment H node787 = injectiveMoment H pivotMatrix787 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix787 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix787 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix787 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix787 (0 : Fin 3) = raw8024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix787 raw8024; decide +kernel
    rw [heq]
    exact (canonical8024 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix787 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix787 (1 : Fin 3) = raw5642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix787 raw5642; decide +kernel
    rw [heq]
    exact (canonical5642 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix787 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix787 (2 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix787 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node787 + (injectiveMoment H (mergeFirst pivotMatrix787 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix787 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix787 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value787, value150, value35, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation788 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-1, 1, 2, -2], ![4, -2, -3, 1]]

theorem sound788 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node788 = Sparse.eval value788 (momentVector H) := by
  have heq : pivotMatrix788 = (fun u v => node788.transpose (pivotPermutation788 u) v) := by apply Matrix.ext; unfold pivotMatrix788 node788 pivotPermutation788; decide +kernel
  have hmoment : injectiveMoment H node788 = injectiveMoment H pivotMatrix788 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix788 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix788 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix788 (0 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix788 (0 : Fin 3) = raw591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix788 raw591; decide +kernel
    rw [heq]
    exact (canonical591 hH).trans (sound89 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix788 (1 : Fin 3)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix788 (1 : Fin 3) = raw4970 := by apply Matrix.ext; unfold mergeFirst pivotMatrix788 raw4970; decide +kernel
    rw [heq]
    exact (canonical4970 hH).trans (sound144 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix788 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix788 (2 : Fin 3) = raw4974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix788 raw4974; decide +kernel
    rw [heq]
    exact (canonical4974 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node788 + (injectiveMoment H (mergeFirst pivotMatrix788 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix788 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix788 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value788, value144, value167, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation789 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix789 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![3, 2, -2, -3]]

theorem sound789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node789 = Sparse.eval value789 (momentVector H) := by
  have heq : pivotMatrix789 = (fun u v => node789.transpose (pivotPermutation789 u) v) := by apply Matrix.ext; unfold pivotMatrix789 node789 pivotPermutation789; decide +kernel
  have hmoment : injectiveMoment H node789 = injectiveMoment H pivotMatrix789 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix789 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix789 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix789 (0 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix789 (0 : Fin 3) = raw337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix789 raw337; decide +kernel
    rw [heq]
    exact (canonical337 hH).trans (sound192 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix789 (1 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix789 (1 : Fin 3) = raw3289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix789 raw3289; decide +kernel
    rw [heq]
    exact (canonical3289 hH).trans (sound162 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix789 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix789 (2 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix789 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node789 + (injectiveMoment H (mergeFirst pivotMatrix789 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix789 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix789 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value789, value162, value192, value197, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation790 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix790 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![3, 2, -2, -3]]

theorem sound790 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node790 = Sparse.eval value790 (momentVector H) := by
  have heq : pivotMatrix790 = (fun u v => node790.transpose (pivotPermutation790 u) v) := by apply Matrix.ext; unfold pivotMatrix790 node790 pivotPermutation790; decide +kernel
  have hmoment : injectiveMoment H node790 = injectiveMoment H pivotMatrix790 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix790 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix790 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix790 (0 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix790 (0 : Fin 3) = raw343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix790 raw343; decide +kernel
    rw [heq]
    exact (canonical343 hH).trans (sound196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix790 (1 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix790 (1 : Fin 3) = raw3648 := by apply Matrix.ext; unfold mergeFirst pivotMatrix790 raw3648; decide +kernel
    rw [heq]
    exact (canonical3648 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix790 (2 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix790 (2 : Fin 3) = raw3674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix790 raw3674; decide +kernel
    rw [heq]
    exact (canonical3674 hH).trans (sound202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node790 + (injectiveMoment H (mergeFirst pivotMatrix790 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix790 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix790 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value790, value167, value196, value202, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation791 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -2, 2, 0], ![3, 2, -3, -2]]

theorem sound791 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node791 = Sparse.eval value791 (momentVector H) := by
  have heq : pivotMatrix791 = (fun u v => node791.transpose (pivotPermutation791 u) v) := by apply Matrix.ext; unfold pivotMatrix791 node791 pivotPermutation791; decide +kernel
  have hmoment : injectiveMoment H node791 = injectiveMoment H pivotMatrix791 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix791 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix791 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix791 (0 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix791 (0 : Fin 3) = raw344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix791 raw344; decide +kernel
    rw [heq]
    exact (canonical344 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix791 (1 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix791 (1 : Fin 3) = raw3649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix791 raw3649; decide +kernel
    rw [heq]
    exact (canonical3649 hH).trans (sound167 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix791 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix791 (2 : Fin 3) = raw3675 := by apply Matrix.ext; unfold mergeFirst pivotMatrix791 raw3675; decide +kernel
    rw [heq]
    exact (canonical3675 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node791 + (injectiveMoment H (mergeFirst pivotMatrix791 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix791 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix791 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value791, value163, value167, value169, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation792 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, -2, 3, -1], ![3, 2, -4, -1]]

theorem sound792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node792 = Sparse.eval value792 (momentVector H) := by
  have heq : pivotMatrix792 = (fun u v => node792.transpose (pivotPermutation792 u) v) := by apply Matrix.ext; unfold pivotMatrix792 node792 pivotPermutation792; decide +kernel
  have hmoment : injectiveMoment H node792 = injectiveMoment H pivotMatrix792 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix792 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix792 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix792 (0 : Fin 3)) =
      Sparse.eval value86 (momentVector H) := by
    have heq : mergeFirst pivotMatrix792 (0 : Fin 3) = raw345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix792 raw345; decide +kernel
    rw [heq]
    exact (canonical345 hH).trans (sound86 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix792 (1 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix792 (1 : Fin 3) = raw3650 := by apply Matrix.ext; unfold mergeFirst pivotMatrix792 raw3650; decide +kernel
    rw [heq]
    exact (canonical3650 hH).trans (sound166 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix792 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix792 (2 : Fin 3) = raw3676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix792 raw3676; decide +kernel
    rw [heq]
    exact (canonical3676 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node792 + (injectiveMoment H (mergeFirst pivotMatrix792 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix792 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix792 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value792, value166, value201, value86, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation793 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, -2, 0, 2], ![3, 2, -2, -3]]

theorem sound793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node793 = Sparse.eval value793 (momentVector H) := by
  have heq : pivotMatrix793 = (fun u v => node793.transpose (pivotPermutation793 u) v) := by apply Matrix.ext; unfold pivotMatrix793 node793 pivotPermutation793; decide +kernel
  have hmoment : injectiveMoment H node793 = injectiveMoment H pivotMatrix793 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix793 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix793 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix793 (0 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix793 (0 : Fin 3) = raw359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix793 raw359; decide +kernel
    rw [heq]
    exact (canonical359 hH).trans (sound163 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix793 (1 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix793 (1 : Fin 3) = raw4169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix793 raw4169; decide +kernel
    rw [heq]
    exact (canonical4169 hH).trans (sound163 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix793 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix793 (2 : Fin 3) = raw4181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix793 raw4181; decide +kernel
    rw [heq]
    exact (canonical4181 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node793 + (injectiveMoment H (mergeFirst pivotMatrix793 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix793 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix793 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value793, value163, value197, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation794 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, -2, 1, 1], ![3, 2, -3, -2]]

theorem sound794 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node794 = Sparse.eval value794 (momentVector H) := by
  have heq : pivotMatrix794 = (fun u v => node794.transpose (pivotPermutation794 u) v) := by apply Matrix.ext; unfold pivotMatrix794 node794 pivotPermutation794; decide +kernel
  have hmoment : injectiveMoment H node794 = injectiveMoment H pivotMatrix794 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix794 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix794 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix794 (0 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix794 (0 : Fin 3) = raw360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix794 raw360; decide +kernel
    rw [heq]
    exact (canonical360 hH).trans (sound196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix794 (1 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix794 (1 : Fin 3) = raw4170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix794 raw4170; decide +kernel
    rw [heq]
    exact (canonical4170 hH).trans (sound162 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix794 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix794 (2 : Fin 3) = raw4182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix794 raw4182; decide +kernel
    rw [heq]
    exact (canonical4182 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node794 + (injectiveMoment H (mergeFirst pivotMatrix794 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix794 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix794 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value794, value162, value169, value196, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation795 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix795 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 2, -4]]

theorem sound795 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node795 = Sparse.eval value795 (momentVector H) := by
  have heq : pivotMatrix795 = (fun u v => node795 (pivotPermutation795 u) v) := by apply Matrix.ext; unfold pivotMatrix795 node795 pivotPermutation795; decide +kernel
  have hmoment : injectiveMoment H node795 = injectiveMoment H pivotMatrix795 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix795 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix795 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix795 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix795 (0 : Fin 3) = raw8069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix795 raw8069; decide +kernel
    rw [heq]
    exact (canonical8069 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix795 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix795 (1 : Fin 3) = raw5728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix795 raw5728; decide +kernel
    rw [heq]
    exact (canonical5728 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix795 (2 : Fin 3)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix795 (2 : Fin 3) = raw5650 := by apply Matrix.ext; unfold mergeFirst pivotMatrix795 raw5650; decide +kernel
    rw [heq]
    exact (canonical5650 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node795 + (injectiveMoment H (mergeFirst pivotMatrix795 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix795 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix795 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value795, value120, value201, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation796 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix796 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem sound796 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node796 = Sparse.eval value796 (momentVector H) := by
  have heq : pivotMatrix796 = (fun u v => node796 (pivotPermutation796 u) v) := by apply Matrix.ext; unfold pivotMatrix796 node796 pivotPermutation796; decide +kernel
  have hmoment : injectiveMoment H node796 = injectiveMoment H pivotMatrix796 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix796 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix796 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix796 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix796 (0 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix796 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix796 (1 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix796 (1 : Fin 3) = raw5686 := by apply Matrix.ext; unfold mergeFirst pivotMatrix796 raw5686; decide +kernel
    rw [heq]
    exact (canonical5686 hH).trans (sound272 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix796 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix796 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix796 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node796 + (injectiveMoment H (mergeFirst pivotMatrix796 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix796 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix796 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value796, value146, value177, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation797 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix797 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem sound797 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node797 = Sparse.eval value797 (momentVector H) := by
  have heq : pivotMatrix797 = (fun u v => node797 (pivotPermutation797 u) v) := by apply Matrix.ext; unfold pivotMatrix797 node797 pivotPermutation797; decide +kernel
  have hmoment : injectiveMoment H node797 = injectiveMoment H pivotMatrix797 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix797 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix797 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix797 (0 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix797 (0 : Fin 3) = raw5633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix797 raw5633; decide +kernel
    rw [heq]
    exact (canonical5633 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix797 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix797 (1 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix797 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix797 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix797 (2 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix797 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node797 + (injectiveMoment H (mergeFirst pivotMatrix797 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix797 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix797 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value797, value181, value215, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation798 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix798 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem sound798 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node798 = Sparse.eval value798 (momentVector H) := by
  have heq : pivotMatrix798 = (fun u v => node798 (pivotPermutation798 u) v) := by apply Matrix.ext; unfold pivotMatrix798 node798 pivotPermutation798; decide +kernel
  have hmoment : injectiveMoment H node798 = injectiveMoment H pivotMatrix798 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix798 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix798 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix798 (0 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix798 (0 : Fin 3) = raw5634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix798 raw5634; decide +kernel
    rw [heq]
    exact (canonical5634 hH).trans (sound190 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix798 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix798 (1 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix798 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix798 (2 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix798 (2 : Fin 3) = raw5723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix798 raw5723; decide +kernel
    rw [heq]
    exact (canonical5723 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node798 + (injectiveMoment H (mergeFirst pivotMatrix798 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix798 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix798 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value798, value190, value215, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation799 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix799 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -2, 0, 3], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem sound799 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node799 = Sparse.eval value799 (momentVector H) := by
  have heq : pivotMatrix799 = (fun u v => node799 (pivotPermutation799 u) v) := by apply Matrix.ext; unfold pivotMatrix799 node799 pivotPermutation799; decide +kernel
  have hmoment : injectiveMoment H node799 = injectiveMoment H pivotMatrix799 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix799 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix799 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix799 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix799 (0 : Fin 3) = raw5636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix799 raw5636; decide +kernel
    rw [heq]
    exact (canonical5636 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix799 (1 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix799 (1 : Fin 3) = raw5724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix799 raw5724; decide +kernel
    rw [heq]
    exact (canonical5724 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix799 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix799 (2 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix799 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node799 + (injectiveMoment H (mergeFirst pivotMatrix799 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix799 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix799 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value799, value185, value204, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation800 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix800 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem sound800 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node800 = Sparse.eval value800 (momentVector H) := by
  have heq : pivotMatrix800 = (fun u v => node800 (pivotPermutation800 u) v) := by apply Matrix.ext; unfold pivotMatrix800 node800 pivotPermutation800; decide +kernel
  have hmoment : injectiveMoment H node800 = injectiveMoment H pivotMatrix800 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix800 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix800 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix800 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix800 (0 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix800 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix800 (1 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix800 (1 : Fin 3) = raw5712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix800 raw5712; decide +kernel
    rw [heq]
    exact (canonical5712 hH).trans (sound285 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix800 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix800 (2 : Fin 3) = raw5705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix800 raw5705; decide +kernel
    rw [heq]
    exact (canonical5705 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node800 + (injectiveMoment H (mergeFirst pivotMatrix800 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix800 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix800 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value800, value206, value229, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation801 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix801 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem sound801 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node801 = Sparse.eval value801 (momentVector H) := by
  have heq : pivotMatrix801 = (fun u v => node801 (pivotPermutation801 u) v) := by apply Matrix.ext; unfold pivotMatrix801 node801 pivotPermutation801; decide +kernel
  have hmoment : injectiveMoment H node801 = injectiveMoment H pivotMatrix801 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix801 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix801 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix801 (0 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix801 (0 : Fin 3) = raw5793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix801 raw5793; decide +kernel
    rw [heq]
    exact (canonical5793 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix801 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix801 (1 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix801 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix801 (2 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix801 (2 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix801 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node801 + (injectiveMoment H (mergeFirst pivotMatrix801 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix801 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix801 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value801, value181, value210, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation802 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix802 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound802 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node802 = Sparse.eval value802 (momentVector H) := by
  have heq : pivotMatrix802 = (fun u v => node802 (pivotPermutation802 u) v) := by apply Matrix.ext; unfold pivotMatrix802 node802 pivotPermutation802; decide +kernel
  have hmoment : injectiveMoment H node802 = injectiveMoment H pivotMatrix802 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix802 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix802 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix802 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix802 (0 : Fin 3) = raw5797 := by apply Matrix.ext; unfold mergeFirst pivotMatrix802 raw5797; decide +kernel
    rw [heq]
    exact (canonical5797 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix802 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix802 (1 : Fin 3) = raw5725 := by apply Matrix.ext; unfold mergeFirst pivotMatrix802 raw5725; decide +kernel
    rw [heq]
    exact (canonical5725 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix802 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix802 (2 : Fin 3) = raw5724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix802 raw5724; decide +kernel
    rw [heq]
    exact (canonical5724 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node802 + (injectiveMoment H (mergeFirst pivotMatrix802 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix802 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix802 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value802, value185, value203, value204, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation803 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix803 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, -2, 0, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem sound803 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node803 = Sparse.eval value803 (momentVector H) := by
  have heq : pivotMatrix803 = (fun u v => node803 (pivotPermutation803 u) v) := by apply Matrix.ext; unfold pivotMatrix803 node803 pivotPermutation803; decide +kernel
  have hmoment : injectiveMoment H node803 = injectiveMoment H pivotMatrix803 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix803 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix803 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix803 (0 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix803 (0 : Fin 3) = raw5800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix803 raw5800; decide +kernel
    rw [heq]
    exact (canonical5800 hH).trans (sound226 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix803 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix803 (1 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix803 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix803 (2 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix803 (2 : Fin 3) = raw5726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix803 raw5726; decide +kernel
    rw [heq]
    exact (canonical5726 hH).trans (sound292 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node803 + (injectiveMoment H (mergeFirst pivotMatrix803 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix803 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix803 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value803, value201, value226, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation804 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 2, -2, 0], ![3, -2, 1, -2]]

theorem sound804 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node804 = Sparse.eval value804 (momentVector H) := by
  have heq : pivotMatrix804 = (fun u v => node804.transpose (pivotPermutation804 u) v) := by apply Matrix.ext; unfold pivotMatrix804 node804 pivotPermutation804; decide +kernel
  have hmoment : injectiveMoment H node804 = injectiveMoment H pivotMatrix804 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix804 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix804 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix804 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (0 : Fin 3) = raw346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw346; decide +kernel
    rw [heq]
    exact (canonical346 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix804 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (1 : Fin 3) = raw3651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw3651; decide +kernel
    rw [heq]
    exact (canonical3651 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix804 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix804 (2 : Fin 3) = raw3847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix804 raw3847; decide +kernel
    rw [heq]
    exact (canonical3847 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node804 + (injectiveMoment H (mergeFirst pivotMatrix804 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix804 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix804 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value804, value184, value198, value203, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation805 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix805 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem sound805 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node805 = Sparse.eval value805 (momentVector H) := by
  have heq : pivotMatrix805 = (fun u v => node805 (pivotPermutation805 u) v) := by apply Matrix.ext; unfold pivotMatrix805 node805 pivotPermutation805; decide +kernel
  have hmoment : injectiveMoment H node805 = injectiveMoment H pivotMatrix805 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix805 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix805 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix805 (0 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix805 (0 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix805 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix805 (1 : Fin 3)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix805 (1 : Fin 3) = raw5718 := by apply Matrix.ext; unfold mergeFirst pivotMatrix805 raw5718; decide +kernel
    rw [heq]
    exact (canonical5718 hH).trans (sound181 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix805 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix805 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix805 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node805 + (injectiveMoment H (mergeFirst pivotMatrix805 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix805 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix805 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value805, value176, value177, value181, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation806 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix806 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0]]

theorem sound806 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node806 = Sparse.eval value806 (momentVector H) := by
  have heq : pivotMatrix806 = (fun u v => node806 (pivotPermutation806 u) v) := by apply Matrix.ext; unfold pivotMatrix806 node806 pivotPermutation806; decide +kernel
  have hmoment : injectiveMoment H node806 = injectiveMoment H pivotMatrix806 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix806 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix806 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix806 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix806 (0 : Fin 3) = raw8093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix806 raw8093; decide +kernel
    rw [heq]
    exact (canonical8093 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix806 (1 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix806 (1 : Fin 3) = raw5730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix806 raw5730; decide +kernel
    rw [heq]
    exact (canonical5730 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix806 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix806 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix806 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node806 + (injectiveMoment H (mergeFirst pivotMatrix806 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix806 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix806 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value806, value177, value204, value41, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation807 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix807 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1]]

theorem sound807 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node807 = Sparse.eval value807 (momentVector H) := by
  have heq : pivotMatrix807 = (fun u v => node807 (pivotPermutation807 u) v) := by apply Matrix.ext; unfold pivotMatrix807 node807 pivotPermutation807; decide +kernel
  have hmoment : injectiveMoment H node807 = injectiveMoment H pivotMatrix807 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix807 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix807 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix807 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix807 (0 : Fin 3) = raw8046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix807 raw8046; decide +kernel
    rw [heq]
    exact (canonical8046 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix807 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix807 (1 : Fin 3) = raw5729 := by apply Matrix.ext; unfold mergeFirst pivotMatrix807 raw5729; decide +kernel
    rw [heq]
    exact (canonical5729 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix807 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix807 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix807 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node807 + (injectiveMoment H (mergeFirst pivotMatrix807 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix807 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix807 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value807, value177, value185, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation808 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 2, 0, -2], ![3, -2, -2, 1]]

theorem sound808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node808 = Sparse.eval value808 (momentVector H) := by
  have heq : pivotMatrix808 = (fun u v => node808.transpose (pivotPermutation808 u) v) := by apply Matrix.ext; unfold pivotMatrix808 node808 pivotPermutation808; decide +kernel
  have hmoment : injectiveMoment H node808 = injectiveMoment H pivotMatrix808 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix808 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix808 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix808 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix808 (0 : Fin 3) = raw362 := by apply Matrix.ext; unfold mergeFirst pivotMatrix808 raw362; decide +kernel
    rw [heq]
    exact (canonical362 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix808 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix808 (1 : Fin 3) = raw4172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix808 raw4172; decide +kernel
    rw [heq]
    exact (canonical4172 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix808 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix808 (2 : Fin 3) = raw4197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix808 raw4197; decide +kernel
    rw [heq]
    exact (canonical4197 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node808 + (injectiveMoment H (mergeFirst pivotMatrix808 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix808 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix808 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value808, value169, value197, value198, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation809 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix809 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 3, -2, -1], ![3, -3, 1, -1]]

theorem sound809 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node809 = Sparse.eval value809 (momentVector H) := by
  have heq : pivotMatrix809 = (fun u v => node809.transpose (pivotPermutation809 u) v) := by apply Matrix.ext; unfold pivotMatrix809 node809 pivotPermutation809; decide +kernel
  have hmoment : injectiveMoment H node809 = injectiveMoment H pivotMatrix809 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix809 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix809 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix809 (0 : Fin 3)) =
      Sparse.eval value98 (momentVector H) := by
    have heq : mergeFirst pivotMatrix809 (0 : Fin 3) = raw347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix809 raw347; decide +kernel
    rw [heq]
    exact (canonical347 hH).trans (sound98 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix809 (1 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix809 (1 : Fin 3) = raw3653 := by apply Matrix.ext; unfold mergeFirst pivotMatrix809 raw3653; decide +kernel
    rw [heq]
    exact (canonical3653 hH).trans (sound187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix809 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix809 (2 : Fin 3) = raw3853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix809 raw3853; decide +kernel
    rw [heq]
    exact (canonical3853 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node809 + (injectiveMoment H (mergeFirst pivotMatrix809 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix809 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix809 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value809, value187, value215, value98, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation810 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix810 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem sound810 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node810 = Sparse.eval value810 (momentVector H) := by
  have heq : pivotMatrix810 = (fun u v => node810 (pivotPermutation810 u) v) := by apply Matrix.ext; unfold pivotMatrix810 node810 pivotPermutation810; decide +kernel
  have hmoment : injectiveMoment H node810 = injectiveMoment H pivotMatrix810 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix810 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix810 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix810 (0 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix810 (0 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix810 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix810 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix810 (1 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix810 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix810 (2 : Fin 3)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix810 (2 : Fin 3) = raw5699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix810 raw5699; decide +kernel
    rw [heq]
    exact (canonical5699 hH).trans (sound93 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node810 + (injectiveMoment H (mergeFirst pivotMatrix810 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix810 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix810 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value810, value188, value215, value93, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation811 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix811 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

theorem sound811 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node811 = Sparse.eval value811 (momentVector H) := by
  have heq : pivotMatrix811 = (fun u v => node811 (pivotPermutation811 u) v) := by apply Matrix.ext; unfold pivotMatrix811 node811 pivotPermutation811; decide +kernel
  have hmoment : injectiveMoment H node811 = injectiveMoment H pivotMatrix811 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix811 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix811 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix811 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix811 (0 : Fin 3) = raw8047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix811 raw8047; decide +kernel
    rw [heq]
    exact (canonical8047 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix811 (1 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix811 (1 : Fin 3) = raw5730 := by apply Matrix.ext; unfold mergeFirst pivotMatrix811 raw5730; decide +kernel
    rw [heq]
    exact (canonical5730 hH).trans (sound204 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix811 (2 : Fin 3)) =
      Sparse.eval value93 (momentVector H) := by
    have heq : mergeFirst pivotMatrix811 (2 : Fin 3) = raw5699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix811 raw5699; decide +kernel
    rw [heq]
    exact (canonical5699 hH).trans (sound93 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node811 + (injectiveMoment H (mergeFirst pivotMatrix811 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix811 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix811 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value811, value204, value37, value93, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation812 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix812 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 3, -1, -2], ![3, -3, -1, 1]]

theorem sound812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node812 = Sparse.eval value812 (momentVector H) := by
  have heq : pivotMatrix812 = (fun u v => node812.transpose (pivotPermutation812 u) v) := by apply Matrix.ext; unfold pivotMatrix812 node812 pivotPermutation812; decide +kernel
  have hmoment : injectiveMoment H node812 = injectiveMoment H pivotMatrix812 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix812 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix812 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix812 (0 : Fin 3)) =
      Sparse.eval value98 (momentVector H) := by
    have heq : mergeFirst pivotMatrix812 (0 : Fin 3) = raw363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix812 raw363; decide +kernel
    rw [heq]
    exact (canonical363 hH).trans (sound98 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix812 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix812 (1 : Fin 3) = raw4174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix812 raw4174; decide +kernel
    rw [heq]
    exact (canonical4174 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix812 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix812 (2 : Fin 3) = raw4201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix812 raw4201; decide +kernel
    rw [heq]
    exact (canonical4201 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node812 + (injectiveMoment H (mergeFirst pivotMatrix812 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix812 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix812 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value812, value170, value198, value98, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation813 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 4, -2, -2], ![3, -4, 1, 0]]

theorem sound813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node813 = Sparse.eval value813 (momentVector H) := by
  have heq : pivotMatrix813 = (fun u v => node813.transpose (pivotPermutation813 u) v) := by apply Matrix.ext; unfold pivotMatrix813 node813 pivotPermutation813; decide +kernel
  have hmoment : injectiveMoment H node813 = injectiveMoment H pivotMatrix813 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix813 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix813 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix813 (0 : Fin 3)) =
      Sparse.eval value99 (momentVector H) := by
    have heq : mergeFirst pivotMatrix813 (0 : Fin 3) = raw348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix813 raw348; decide +kernel
    rw [heq]
    exact (canonical348 hH).trans (sound99 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix813 (1 : Fin 3)) =
      Sparse.eval value190 (momentVector H) := by
    have heq : mergeFirst pivotMatrix813 (1 : Fin 3) = raw3654 := by apply Matrix.ext; unfold mergeFirst pivotMatrix813 raw3654; decide +kernel
    rw [heq]
    exact (canonical3654 hH).trans (sound190 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix813 (2 : Fin 3)) =
      Sparse.eval value218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix813 (2 : Fin 3) = raw3854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix813 raw3854; decide +kernel
    rw [heq]
    exact (canonical3854 hH).trans (sound218 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node813 + (injectiveMoment H (mergeFirst pivotMatrix813 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix813 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix813 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value813, value190, value218, value99, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation814 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix814 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 4, -2, -2], ![3, -4, 0, 1]]

theorem sound814 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node814 = Sparse.eval value814 (momentVector H) := by
  have heq : pivotMatrix814 = (fun u v => node814.transpose (pivotPermutation814 u) v) := by apply Matrix.ext; unfold pivotMatrix814 node814 pivotPermutation814; decide +kernel
  have hmoment : injectiveMoment H node814 = injectiveMoment H pivotMatrix814 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix814 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix814 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix814 (0 : Fin 3)) =
      Sparse.eval value99 (momentVector H) := by
    have heq : mergeFirst pivotMatrix814 (0 : Fin 3) = raw364 := by apply Matrix.ext; unfold mergeFirst pivotMatrix814 raw364; decide +kernel
    rw [heq]
    exact (canonical364 hH).trans (sound99 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix814 (1 : Fin 3)) =
      Sparse.eval value171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix814 (1 : Fin 3) = raw4176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix814 raw4176; decide +kernel
    rw [heq]
    exact (canonical4176 hH).trans (sound171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix814 (2 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix814 (2 : Fin 3) = raw4204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix814 raw4204; decide +kernel
    rw [heq]
    exact (canonical4204 hH).trans (sound199 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node814 + (injectiveMoment H (mergeFirst pivotMatrix814 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix814 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix814 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value814, value171, value199, value99, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation815 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix815 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -2, 1, 1], ![3, 1, -2, -2]]

theorem sound815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node815 = Sparse.eval value815 (momentVector H) := by
  have heq : pivotMatrix815 = (fun u v => node815.transpose (pivotPermutation815 u) v) := by apply Matrix.ext; unfold pivotMatrix815 node815 pivotPermutation815; decide +kernel
  have hmoment : injectiveMoment H node815 = injectiveMoment H pivotMatrix815 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix815 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix815 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix815 (0 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix815 (0 : Fin 3) = raw592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix815 raw592; decide +kernel
    rw [heq]
    exact (canonical592 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix815 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix815 (1 : Fin 3) = raw4971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix815 raw4971; decide +kernel
    rw [heq]
    exact (canonical4971 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix815 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix815 (2 : Fin 3) = raw4981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix815 raw4981; decide +kernel
    rw [heq]
    exact (canonical4981 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node815 + (injectiveMoment H (mergeFirst pivotMatrix815 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix815 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix815 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value815, value184, value210, value223, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation816 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix816 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3]]

theorem sound816 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node816 = Sparse.eval value816 (momentVector H) := by
  have heq : pivotMatrix816 = (fun u v => node816 (pivotPermutation816 u) v) := by apply Matrix.ext; unfold pivotMatrix816 node816 pivotPermutation816; decide +kernel
  have hmoment : injectiveMoment H node816 = injectiveMoment H pivotMatrix816 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix816 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix816 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix816 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix816 (0 : Fin 3) = raw8099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix816 raw8099; decide +kernel
    rw [heq]
    exact (canonical8099 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix816 (1 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix816 (1 : Fin 3) = raw5732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix816 raw5732; decide +kernel
    rw [heq]
    exact (canonical5732 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix816 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix816 (2 : Fin 3) = raw5705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix816 raw5705; decide +kernel
    rw [heq]
    exact (canonical5705 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node816 + (injectiveMoment H (mergeFirst pivotMatrix816 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix816 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix816 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value816, value206, value215, value36, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation817 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix817 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

theorem sound817 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node817 = Sparse.eval value817 (momentVector H) := by
  have heq : pivotMatrix817 = (fun u v => node817 (pivotPermutation817 u) v) := by apply Matrix.ext; unfold pivotMatrix817 node817 pivotPermutation817; decide +kernel
  have hmoment : injectiveMoment H node817 = injectiveMoment H pivotMatrix817 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix817 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix817 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix817 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix817 (0 : Fin 3) = raw8048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix817 raw8048; decide +kernel
    rw [heq]
    exact (canonical8048 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix817 (1 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix817 (1 : Fin 3) = raw5731 := by apply Matrix.ext; unfold mergeFirst pivotMatrix817 raw5731; decide +kernel
    rw [heq]
    exact (canonical5731 hH).trans (sound87 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix817 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix817 (2 : Fin 3) = raw5705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix817 raw5705; decide +kernel
    rw [heq]
    exact (canonical5705 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node817 + (injectiveMoment H (mergeFirst pivotMatrix817 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix817 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix817 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value817, value206, value40, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation818 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix818 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 0, 3], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem sound818 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node818 = Sparse.eval value818 (momentVector H) := by
  have heq : pivotMatrix818 = (fun u v => node818 (pivotPermutation818 u) v) := by apply Matrix.ext; unfold pivotMatrix818 node818 pivotPermutation818; decide +kernel
  have hmoment : injectiveMoment H node818 = injectiveMoment H pivotMatrix818 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix818 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix818 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix818 (0 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix818 (0 : Fin 3) = raw6329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix818 raw6329; decide +kernel
    rw [heq]
    exact (canonical6329 hH).trans (sound173 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix818 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix818 (1 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix818 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix818 (2 : Fin 3)) =
      Sparse.eval value87 (momentVector H) := by
    have heq : mergeFirst pivotMatrix818 (2 : Fin 3) = raw5723 := by apply Matrix.ext; unfold mergeFirst pivotMatrix818 raw5723; decide +kernel
    rw [heq]
    exact (canonical5723 hH).trans (sound87 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node818 + (injectiveMoment H (mergeFirst pivotMatrix818 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix818 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix818 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value818, value173, value201, value87, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation819 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix819 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 0, 3], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem sound819 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node819 = Sparse.eval value819 (momentVector H) := by
  have heq : pivotMatrix819 = (fun u v => node819 (pivotPermutation819 u) v) := by apply Matrix.ext; unfold pivotMatrix819 node819 pivotPermutation819; decide +kernel
  have hmoment : injectiveMoment H node819 = injectiveMoment H pivotMatrix819 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix819 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix819 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix819 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix819 (0 : Fin 3) = raw6552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix819 raw6552; decide +kernel
    rw [heq]
    exact (canonical6552 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix819 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix819 (1 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix819 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix819 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix819 (2 : Fin 3) = raw5722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix819 raw5722; decide +kernel
    rw [heq]
    exact (canonical5722 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node819 + (injectiveMoment H (mergeFirst pivotMatrix819 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix819 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix819 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value819, value185, value201, value215, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation820 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 1, 1, -2], ![3, -2, -2, 1]]

theorem sound820 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node820 = Sparse.eval value820 (momentVector H) := by
  have heq : pivotMatrix820 = (fun u v => node820.transpose (pivotPermutation820 u) v) := by apply Matrix.ext; unfold pivotMatrix820 node820 pivotPermutation820; decide +kernel
  have hmoment : injectiveMoment H node820 = injectiveMoment H pivotMatrix820 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix820 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix820 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix820 (0 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix820 (0 : Fin 3) = raw593 := by apply Matrix.ext; unfold mergeFirst pivotMatrix820 raw593; decide +kernel
    rw [heq]
    exact (canonical593 hH).trans (sound223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix820 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix820 (1 : Fin 3) = raw4973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix820 raw4973; decide +kernel
    rw [heq]
    exact (canonical4973 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix820 (2 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix820 (2 : Fin 3) = raw5041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix820 raw5041; decide +kernel
    rw [heq]
    exact (canonical5041 hH).trans (sound202 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node820 + (injectiveMoment H (mergeFirst pivotMatrix820 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix820 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix820 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value820, value175, value202, value223, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation821 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![1, -1, 2, -2], ![2, 2, -4, 0]]

theorem sound821 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node821 = Sparse.eval value821 (momentVector H) := by
  have heq : pivotMatrix821 = (fun u v => node821.transpose (pivotPermutation821 u) v) := by apply Matrix.ext; unfold pivotMatrix821 node821 pivotPermutation821; decide +kernel
  have hmoment : injectiveMoment H node821 = injectiveMoment H pivotMatrix821 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix821 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix821 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix821 (0 : Fin 3)) =
      Sparse.eval value136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix821 (0 : Fin 3) = raw265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix821 raw265; decide +kernel
    rw [heq]
    exact (canonical265 hH).trans (sound136 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix821 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix821 (1 : Fin 3) = raw2549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix821 raw2549; decide +kernel
    rw [heq]
    exact (canonical2549 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix821 (2 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix821 (2 : Fin 3) = raw2647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix821 raw2647; decide +kernel
    rw [heq]
    exact (canonical2647 hH).trans (sound134 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node821 + (injectiveMoment H (mergeFirst pivotMatrix821 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix821 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix821 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value821, value134, value136, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation822 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 1, 2], ![1, 2, -2, -1], ![2, -1, 1, -2]]

theorem sound822 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node822 = Sparse.eval value822 (momentVector H) := by
  have heq : pivotMatrix822 = (fun u v => node822.transpose (pivotPermutation822 u) v) := by apply Matrix.ext; unfold pivotMatrix822 node822 pivotPermutation822; decide +kernel
  have hmoment : injectiveMoment H node822 = injectiveMoment H pivotMatrix822 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix822 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix822 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix822 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix822 (0 : Fin 3) = raw262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix822 raw262; decide +kernel
    rw [heq]
    exact (canonical262 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix822 (1 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix822 (1 : Fin 3) = raw2488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix822 raw2488; decide +kernel
    rw [heq]
    exact (canonical2488 hH).trans (sound224 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix822 (2 : Fin 3)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix822 (2 : Fin 3) = raw2521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix822 raw2521; decide +kernel
    rw [heq]
    exact (canonical2521 hH).trans (sound276 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node822 + (injectiveMoment H (mergeFirst pivotMatrix822 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix822 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix822 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value822, value159, value224, value276, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation823 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix823 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 2, 1], ![1, 2, -3, 0], ![2, -1, 1, -2]]

theorem sound823 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node823 = Sparse.eval value823 (momentVector H) := by
  have heq : pivotMatrix823 = (fun u v => node823.transpose (pivotPermutation823 u) v) := by apply Matrix.ext; unfold pivotMatrix823 node823 pivotPermutation823; decide +kernel
  have hmoment : injectiveMoment H node823 = injectiveMoment H pivotMatrix823 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix823 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix823 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix823 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix823 (0 : Fin 3) = raw266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix823 raw266; decide +kernel
    rw [heq]
    exact (canonical266 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix823 (1 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix823 (1 : Fin 3) = raw2625 := by apply Matrix.ext; unfold mergeFirst pivotMatrix823 raw2625; decide +kernel
    rw [heq]
    exact (canonical2625 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix823 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix823 (2 : Fin 3) = raw2648 := by apply Matrix.ext; unfold mergeFirst pivotMatrix823 raw2648; decide +kernel
    rw [heq]
    exact (canonical2648 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node823 + (injectiveMoment H (mergeFirst pivotMatrix823 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix823 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix823 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value823, value103, value111, value261, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation824 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix824 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, -1, 3, 0], ![1, 2, -1, -2], ![2, -1, -2, 1]]

theorem sound824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node824 = Sparse.eval value824 (momentVector H) := by
  have heq : pivotMatrix824 = (fun u v => node824.transpose (pivotPermutation824 u) v) := by apply Matrix.ext; unfold pivotMatrix824 node824 pivotPermutation824; decide +kernel
  have hmoment : injectiveMoment H node824 = injectiveMoment H pivotMatrix824 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix824 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix824 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix824 (0 : Fin 3)) =
      Sparse.eval value159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix824 (0 : Fin 3) = raw268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix824 raw268; decide +kernel
    rw [heq]
    exact (canonical268 hH).trans (sound159 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix824 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix824 (1 : Fin 3) = raw2869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix824 raw2869; decide +kernel
    rw [heq]
    exact (canonical2869 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix824 (2 : Fin 3)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix824 (2 : Fin 3) = raw2871 := by apply Matrix.ext; unfold mergeFirst pivotMatrix824 raw2871; decide +kernel
    rw [heq]
    exact (canonical2871 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node824 + (injectiveMoment H (mergeFirst pivotMatrix824 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix824 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix824 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value824, value111, value159, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation825 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![1, -2, 2, -1], ![2, 2, -2, -2]]

theorem sound825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node825 = Sparse.eval value825 (momentVector H) := by
  have heq : pivotMatrix825 = (fun u v => node825.transpose (pivotPermutation825 u) v) := by apply Matrix.ext; unfold pivotMatrix825 node825 pivotPermutation825; decide +kernel
  have hmoment : injectiveMoment H node825 = injectiveMoment H pivotMatrix825 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix825 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix825 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix825 (0 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix825 (0 : Fin 3) = raw338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix825 raw338; decide +kernel
    rw [heq]
    exact (canonical338 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix825 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix825 (1 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix825 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix825 (2 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix825 (2 : Fin 3) = raw3638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix825 raw3638; decide +kernel
    rw [heq]
    exact (canonical3638 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node825 + (injectiveMoment H (mergeFirst pivotMatrix825 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix825 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix825 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value825, value101, value197, value224, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation826 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix826 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

theorem sound826 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node826 = Sparse.eval value826 (momentVector H) := by
  have heq : pivotMatrix826 = (fun u v => node826 (pivotPermutation826 u) v) := by apply Matrix.ext; unfold pivotMatrix826 node826 pivotPermutation826; decide +kernel
  have hmoment : injectiveMoment H node826 = injectiveMoment H pivotMatrix826 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix826 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix826 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix826 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix826 (0 : Fin 3) = raw6437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix826 raw6437; decide +kernel
    rw [heq]
    exact (canonical6437 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix826 (1 : Fin 3)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix826 (1 : Fin 3) = raw5775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix826 raw5775; decide +kernel
    rw [heq]
    exact (canonical5775 hH).trans (sound106 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix826 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix826 (2 : Fin 3) = raw5741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix826 raw5741; decide +kernel
    rw [heq]
    exact (canonical5741 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node826 + (injectiveMoment H (mergeFirst pivotMatrix826 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix826 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix826 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value826, value106, value145, value146, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation827 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix827 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-1, -2, 1, 2], ![0, 0, -2, 2], ![1, 1, 1, -3]]

theorem sound827 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node827 = Sparse.eval value827 (momentVector H) := by
  have heq : pivotMatrix827 = (fun u v => node827 (pivotPermutation827 u) v) := by apply Matrix.ext; unfold pivotMatrix827 node827 pivotPermutation827; decide +kernel
  have hmoment : injectiveMoment H node827 = injectiveMoment H pivotMatrix827 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix827 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix827 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix827 (0 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix827 (0 : Fin 3) = raw6640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix827 raw6640; decide +kernel
    rw [heq]
    exact (canonical6640 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix827 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix827 (1 : Fin 3) = raw5780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix827 raw5780; decide +kernel
    rw [heq]
    exact (canonical5780 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix827 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix827 (2 : Fin 3) = raw5741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix827 raw5741; decide +kernel
    rw [heq]
    exact (canonical5741 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node827 + (injectiveMoment H (mergeFirst pivotMatrix827 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix827 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix827 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value827, value146, value176, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation828 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix828 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -2, 1, 0], ![2, 2, -2, -2]]

theorem sound828 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node828 = Sparse.eval value828 (momentVector H) := by
  have heq : pivotMatrix828 = (fun u v => node828.transpose (pivotPermutation828 u) v) := by apply Matrix.ext; unfold pivotMatrix828 node828 pivotPermutation828; decide +kernel
  have hmoment : injectiveMoment H node828 = injectiveMoment H pivotMatrix828 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix828 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix828 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix828 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix828 (0 : Fin 3) = raw349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix828 raw349; decide +kernel
    rw [heq]
    exact (canonical349 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix828 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix828 (1 : Fin 3) = raw3674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix828 raw3674; decide +kernel
    rw [heq]
    exact (canonical3674 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix828 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix828 (2 : Fin 3) = raw3858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix828 raw3858; decide +kernel
    rw [heq]
    exact (canonical3858 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node828 + (injectiveMoment H (mergeFirst pivotMatrix828 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix828 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix828 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value828, value202, value210, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation829 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix829 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -2, 2, -1], ![2, 2, -3, -1]]

theorem sound829 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node829 = Sparse.eval value829 (momentVector H) := by
  have heq : pivotMatrix829 = (fun u v => node829.transpose (pivotPermutation829 u) v) := by apply Matrix.ext; unfold pivotMatrix829 node829 pivotPermutation829; decide +kernel
  have hmoment : injectiveMoment H node829 = injectiveMoment H pivotMatrix829 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix829 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix829 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix829 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix829 (0 : Fin 3) = raw350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix829 raw350; decide +kernel
    rw [heq]
    exact (canonical350 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix829 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix829 (1 : Fin 3) = raw3675 := by apply Matrix.ext; unfold mergeFirst pivotMatrix829 raw3675; decide +kernel
    rw [heq]
    exact (canonical3675 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix829 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix829 (2 : Fin 3) = raw3859 := by apply Matrix.ext; unfold mergeFirst pivotMatrix829 raw3859; decide +kernel
    rw [heq]
    exact (canonical3859 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node829 + (injectiveMoment H (mergeFirst pivotMatrix829 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix829 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix829 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value829, value103, value169, value226, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation830 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix830 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![1, -2, 3, -2], ![2, 2, -4, 0]]

theorem sound830 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node830 = Sparse.eval value830 (momentVector H) := by
  have heq : pivotMatrix830 = (fun u v => node830.transpose (pivotPermutation830 u) v) := by apply Matrix.ext; unfold pivotMatrix830 node830 pivotPermutation830; decide +kernel
  have hmoment : injectiveMoment H node830 = injectiveMoment H pivotMatrix830 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix830 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix830 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix830 (0 : Fin 3)) =
      Sparse.eval value104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix830 (0 : Fin 3) = raw351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix830 raw351; decide +kernel
    rw [heq]
    exact (canonical351 hH).trans (sound104 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix830 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix830 (1 : Fin 3) = raw3676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix830 raw3676; decide +kernel
    rw [heq]
    exact (canonical3676 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix830 (2 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix830 (2 : Fin 3) = raw3860 := by apply Matrix.ext; unfold mergeFirst pivotMatrix830 raw3860; decide +kernel
    rw [heq]
    exact (canonical3860 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node830 + (injectiveMoment H (mergeFirst pivotMatrix830 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix830 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix830 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value830, value104, value201, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation831 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix831 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![1, -2, 0, 1], ![2, 2, -2, -2]]

theorem sound831 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node831 = Sparse.eval value831 (momentVector H) := by
  have heq : pivotMatrix831 = (fun u v => node831.transpose (pivotPermutation831 u) v) := by apply Matrix.ext; unfold pivotMatrix831 node831 pivotPermutation831; decide +kernel
  have hmoment : injectiveMoment H node831 = injectiveMoment H pivotMatrix831 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix831 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix831 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix831 (0 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix831 (0 : Fin 3) = raw365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix831 raw365; decide +kernel
    rw [heq]
    exact (canonical365 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix831 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix831 (1 : Fin 3) = raw4181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix831 raw4181; decide +kernel
    rw [heq]
    exact (canonical4181 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix831 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix831 (2 : Fin 3) = raw4208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix831 raw4208; decide +kernel
    rw [heq]
    exact (canonical4208 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node831 + (injectiveMoment H (mergeFirst pivotMatrix831 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix831 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix831 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value831, value197, value203, value212, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
