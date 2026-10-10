import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical183

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation384 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix384 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem sound384 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node384 = Sparse.eval value384 (momentVector H) := by
  have heq : pivotMatrix384 = (fun u v => node384 (pivotPermutation384 u) v) := by apply Matrix.ext; unfold pivotMatrix384 node384 pivotPermutation384; decide +kernel
  have hmoment : injectiveMoment H node384 = injectiveMoment H pivotMatrix384 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix384 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix384 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix384 (0 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix384 (0 : Fin 4) = raw1403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix384 raw1403; decide +kernel
    rw [heq]
    exact (canonical1403 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix384 (1 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix384 (1 : Fin 4) = raw950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix384 raw950; decide +kernel
    rw [heq]
    exact (canonical950 hH).trans (sound120 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix384 (2 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix384 (2 : Fin 4) = raw940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix384 raw940; decide +kernel
    rw [heq]
    exact (canonical940 hH).trans (sound120 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix384 (3 : Fin 4)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix384 (3 : Fin 4) = raw936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix384 raw936; decide +kernel
    rw [heq]
    exact (canonical936 hH).trans (sound119 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node384 + (injectiveMoment H (mergeFirst pivotMatrix384 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix384 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix384 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix384 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value384, value119, value120, value145, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation385 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix385 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem sound385 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node385 = Sparse.eval value385 (momentVector H) := by
  have heq : pivotMatrix385 = (fun u v => node385 (pivotPermutation385 u) v) := by apply Matrix.ext; unfold pivotMatrix385 node385 pivotPermutation385; decide +kernel
  have hmoment : injectiveMoment H node385 = injectiveMoment H pivotMatrix385 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix385 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix385 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix385 (0 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix385 (0 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix385 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix385 (1 : Fin 4)) =
      Sparse.eval value125 (momentVector H) := by
    have heq : mergeFirst pivotMatrix385 (1 : Fin 4) = raw951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix385 raw951; decide +kernel
    rw [heq]
    exact (canonical951 hH).trans (sound125 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix385 (2 : Fin 4)) =
      Sparse.eval value121 (momentVector H) := by
    have heq : mergeFirst pivotMatrix385 (2 : Fin 4) = raw942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix385 raw942; decide +kernel
    rw [heq]
    exact (canonical942 hH).trans (sound121 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix385 (3 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix385 (3 : Fin 4) = raw940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix385 raw940; decide +kernel
    rw [heq]
    exact (canonical940 hH).trans (sound120 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node385 + (injectiveMoment H (mergeFirst pivotMatrix385 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix385 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix385 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix385 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value385, value120, value121, value125, value146, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation386 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix386 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node386 = Sparse.eval value386 (momentVector H) := by
  have heq : pivotMatrix386 = (fun u v => node386 (pivotPermutation386 u) v) := by apply Matrix.ext; unfold pivotMatrix386 node386 pivotPermutation386; decide +kernel
  have hmoment : injectiveMoment H node386 = injectiveMoment H pivotMatrix386 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix386 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix386 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix386 (0 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix386 (0 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix386 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix386 (1 : Fin 4)) =
      Sparse.eval value126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix386 (1 : Fin 4) = raw952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix386 raw952; decide +kernel
    rw [heq]
    exact (canonical952 hH).trans (sound126 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix386 (2 : Fin 4)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix386 (2 : Fin 4) = raw944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix386 raw944; decide +kernel
    rw [heq]
    exact (canonical944 hH).trans (sound123 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix386 (3 : Fin 4)) =
      Sparse.eval value122 (momentVector H) := by
    have heq : mergeFirst pivotMatrix386 (3 : Fin 4) = raw943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix386 raw943; decide +kernel
    rw [heq]
    exact (canonical943 hH).trans (sound122 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node386 + (injectiveMoment H (mergeFirst pivotMatrix386 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix386 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix386 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix386 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value386, value122, value123, value126, value149, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation387 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix387 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node387 = Sparse.eval value387 (momentVector H) := by
  have heq : pivotMatrix387 = (fun u v => node387 (pivotPermutation387 u) v) := by apply Matrix.ext; unfold pivotMatrix387 node387 pivotPermutation387; decide +kernel
  have hmoment : injectiveMoment H node387 = injectiveMoment H pivotMatrix387 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix387 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix387 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix387 (0 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix387 (0 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix387 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix387 (1 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix387 (1 : Fin 4) = raw953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix387 raw953; decide +kernel
    rw [heq]
    exact (canonical953 hH).trans (sound127 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix387 (2 : Fin 4)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix387 (2 : Fin 4) = raw945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix387 raw945; decide +kernel
    rw [heq]
    exact (canonical945 hH).trans (sound124 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix387 (3 : Fin 4)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix387 (3 : Fin 4) = raw944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix387 raw944; decide +kernel
    rw [heq]
    exact (canonical944 hH).trans (sound123 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node387 + (injectiveMoment H (mergeFirst pivotMatrix387 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix387 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix387 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix387 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value387, value123, value124, value127, value150, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation388 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix388 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound388 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node388 = Sparse.eval value388 (momentVector H) := by
  have heq : pivotMatrix388 = (fun u v => node388 (pivotPermutation388 u) v) := by apply Matrix.ext; unfold pivotMatrix388 node388 pivotPermutation388; decide +kernel
  have hmoment : injectiveMoment H node388 = injectiveMoment H pivotMatrix388 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix388 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix388 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix388 (0 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix388 (0 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix388 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix388 (1 : Fin 4)) =
      Sparse.eval value128 (momentVector H) := by
    have heq : mergeFirst pivotMatrix388 (1 : Fin 4) = raw956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix388 raw956; decide +kernel
    rw [heq]
    exact (canonical956 hH).trans (sound128 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix388 (2 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix388 (2 : Fin 4) = raw953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix388 raw953; decide +kernel
    rw [heq]
    exact (canonical953 hH).trans (sound127 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix388 (3 : Fin 4)) =
      Sparse.eval value126 (momentVector H) := by
    have heq : mergeFirst pivotMatrix388 (3 : Fin 4) = raw952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix388 raw952; decide +kernel
    rw [heq]
    exact (canonical952 hH).trans (sound126 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node388 + (injectiveMoment H (mergeFirst pivotMatrix388 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix388 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix388 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix388 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value388, value126, value127, value128, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation389 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix389 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node389 = Sparse.eval value389 (momentVector H) := by
  have heq : pivotMatrix389 = (fun u v => node389 (pivotPermutation389 u) v) := by apply Matrix.ext; unfold pivotMatrix389 node389 pivotPermutation389; decide +kernel
  have hmoment : injectiveMoment H node389 = injectiveMoment H pivotMatrix389 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix389 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix389 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix389 (0 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix389 (0 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix389 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix389 (1 : Fin 4)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix389 (1 : Fin 4) = raw957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix389 raw957; decide +kernel
    rw [heq]
    exact (canonical957 hH).trans (sound129 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix389 (2 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix389 (2 : Fin 4) = raw954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix389 raw954; decide +kernel
    rw [heq]
    exact (canonical954 hH).trans (sound127 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix389 (3 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix389 (3 : Fin 4) = raw953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix389 raw953; decide +kernel
    rw [heq]
    exact (canonical953 hH).trans (sound127 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node389 + (injectiveMoment H (mergeFirst pivotMatrix389 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix389 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix389 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix389 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value389, value127, value129, value145, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation390 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix390 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound390 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node390 = Sparse.eval value390 (momentVector H) := by
  have heq : pivotMatrix390 = (fun u v => node390 (pivotPermutation390 u) v) := by apply Matrix.ext; unfold pivotMatrix390 node390 pivotPermutation390; decide +kernel
  have hmoment : injectiveMoment H node390 = injectiveMoment H pivotMatrix390 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix390 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix390 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix390 (0 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix390 (0 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix390 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix390 (1 : Fin 4)) =
      Sparse.eval value130 (momentVector H) := by
    have heq : mergeFirst pivotMatrix390 (1 : Fin 4) = raw959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix390 raw959; decide +kernel
    rw [heq]
    exact (canonical959 hH).trans (sound130 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix390 (2 : Fin 4)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix390 (2 : Fin 4) = raw957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix390 raw957; decide +kernel
    rw [heq]
    exact (canonical957 hH).trans (sound129 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix390 (3 : Fin 4)) =
      Sparse.eval value128 (momentVector H) := by
    have heq : mergeFirst pivotMatrix390 (3 : Fin 4) = raw956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix390 raw956; decide +kernel
    rw [heq]
    exact (canonical956 hH).trans (sound128 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node390 + (injectiveMoment H (mergeFirst pivotMatrix390 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix390 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix390 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix390 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value390, value128, value129, value130, value155, Sparse.eval] at hc ⊢
  linarith

theorem sound391 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node391 = Sparse.eval value391 (momentVector H) := by
  have hc : momentVector H 279 = injectiveMoment H node391 := rfl
  simp [value391, Sparse.eval, hc]

theorem sound392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node392 = Sparse.eval value392 (momentVector H) := by
  have hc : momentVector H 280 = injectiveMoment H node392 := rfl
  simp [value392, Sparse.eval, hc]

theorem sound393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node393 = Sparse.eval value393 (momentVector H) := by
  have hc : momentVector H 281 = injectiveMoment H node393 := rfl
  simp [value393, Sparse.eval, hc]

theorem sound394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node394 = Sparse.eval value394 (momentVector H) := by
  have hc : momentVector H 282 = injectiveMoment H node394 := rfl
  simp [value394, Sparse.eval, hc]

theorem sound395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node395 = Sparse.eval value395 (momentVector H) := by
  have hc : momentVector H 72 = injectiveMoment H node395 := rfl
  simp [value395, Sparse.eval, hc]

theorem sound396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node396 = Sparse.eval value396 (momentVector H) := by
  have hc : momentVector H 73 = injectiveMoment H node396 := rfl
  simp [value396, Sparse.eval, hc]

theorem sound397 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node397 = Sparse.eval value397 (momentVector H) := by
  have hc : momentVector H 74 = injectiveMoment H node397 := rfl
  simp [value397, Sparse.eval, hc]

theorem sound398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node398 = Sparse.eval value398 (momentVector H) := by
  have hc : momentVector H 75 = injectiveMoment H node398 := rfl
  simp [value398, Sparse.eval, hc]

theorem sound399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node399 = Sparse.eval value399 (momentVector H) := by
  have hc : momentVector H 284 = injectiveMoment H node399 := rfl
  simp [value399, Sparse.eval, hc]

theorem sound400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node400 = Sparse.eval value400 (momentVector H) := by
  have hc : momentVector H 286 = injectiveMoment H node400 := rfl
  simp [value400, Sparse.eval, hc]

theorem sound401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node401 = Sparse.eval value401 (momentVector H) := by
  have hc : momentVector H 287 = injectiveMoment H node401 := rfl
  simp [value401, Sparse.eval, hc]

theorem sound402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node402 = Sparse.eval value402 (momentVector H) := by
  have hc : momentVector H 288 = injectiveMoment H node402 := rfl
  simp [value402, Sparse.eval, hc]

theorem sound403 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node403 = Sparse.eval value403 (momentVector H) := by
  have hc : momentVector H 289 = injectiveMoment H node403 := rfl
  simp [value403, Sparse.eval, hc]

theorem sound404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node404 = Sparse.eval value404 (momentVector H) := by
  have hc : momentVector H 76 = injectiveMoment H node404 := rfl
  simp [value404, Sparse.eval, hc]

theorem sound405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node405 = Sparse.eval value405 (momentVector H) := by
  have hc : momentVector H 290 = injectiveMoment H node405 := rfl
  simp [value405, Sparse.eval, hc]

theorem sound406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node406 = Sparse.eval value406 (momentVector H) := by
  have hc : momentVector H 291 = injectiveMoment H node406 := rfl
  simp [value406, Sparse.eval, hc]

theorem sound407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node407 = Sparse.eval value407 (momentVector H) := by
  have hc : momentVector H 293 = injectiveMoment H node407 := rfl
  simp [value407, Sparse.eval, hc]

theorem sound408 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node408 = Sparse.eval value408 (momentVector H) := by
  have hc : momentVector H 77 = injectiveMoment H node408 := rfl
  simp [value408, Sparse.eval, hc]

theorem sound409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node409 = Sparse.eval value409 (momentVector H) := by
  have hc : momentVector H 78 = injectiveMoment H node409 := rfl
  simp [value409, Sparse.eval, hc]

theorem sound410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node410 = Sparse.eval value410 (momentVector H) := by
  have hc : momentVector H 299 = injectiveMoment H node410 := rfl
  simp [value410, Sparse.eval, hc]

theorem sound411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node411 = Sparse.eval value411 (momentVector H) := by
  have hc : momentVector H 300 = injectiveMoment H node411 := rfl
  simp [value411, Sparse.eval, hc]

theorem sound412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node412 = Sparse.eval value412 (momentVector H) := by
  have hc : momentVector H 79 = injectiveMoment H node412 := rfl
  simp [value412, Sparse.eval, hc]

theorem sound413 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node413 = Sparse.eval value413 (momentVector H) := by
  have hc : momentVector H 80 = injectiveMoment H node413 := rfl
  simp [value413, Sparse.eval, hc]

def pivotPermutation414 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem sound414 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node414 = Sparse.eval value414 (momentVector H) := by
  have heq : pivotMatrix414 = (fun u v => node414 (pivotPermutation414 u) v) := by apply Matrix.ext; unfold pivotMatrix414 node414 pivotPermutation414; decide +kernel
  have hmoment : injectiveMoment H node414 = injectiveMoment H pivotMatrix414 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix414 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix414 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix414 (0 : Fin 4)) =
      Sparse.eval value71 (momentVector H) := by
    have heq : mergeFirst pivotMatrix414 (0 : Fin 4) = raw227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix414 raw227; decide +kernel
    rw [heq]
    exact (canonical227 hH).trans (sound71 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix414 (1 : Fin 4)) =
      Sparse.eval value131 (momentVector H) := by
    have heq : mergeFirst pivotMatrix414 (1 : Fin 4) = raw1340 := by apply Matrix.ext; unfold mergeFirst pivotMatrix414 raw1340; decide +kernel
    rw [heq]
    exact (canonical1340 hH).trans (sound131 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix414 (2 : Fin 4)) =
      Sparse.eval value139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix414 (2 : Fin 4) = raw1392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix414 raw1392; decide +kernel
    rw [heq]
    exact (canonical1392 hH).trans (sound139 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix414 (3 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix414 (3 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix414 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node414 + (injectiveMoment H (mergeFirst pivotMatrix414 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix414 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix414 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix414 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value414, value131, value139, value149, value71, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation415 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem sound415 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node415 = Sparse.eval value415 (momentVector H) := by
  have heq : pivotMatrix415 = (fun u v => node415 (pivotPermutation415 u) v) := by apply Matrix.ext; unfold pivotMatrix415 node415 pivotPermutation415; decide +kernel
  have hmoment : injectiveMoment H node415 = injectiveMoment H pivotMatrix415 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix415 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix415 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix415 (0 : Fin 4)) =
      Sparse.eval value72 (momentVector H) := by
    have heq : mergeFirst pivotMatrix415 (0 : Fin 4) = raw231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix415 raw231; decide +kernel
    rw [heq]
    exact (canonical231 hH).trans (sound72 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix415 (1 : Fin 4)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix415 (1 : Fin 4) = raw1341 := by apply Matrix.ext; unfold mergeFirst pivotMatrix415 raw1341; decide +kernel
    rw [heq]
    exact (canonical1341 hH).trans (sound132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix415 (2 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix415 (2 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix415 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix415 (3 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix415 (3 : Fin 4) = raw1419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix415 raw1419; decide +kernel
    rw [heq]
    exact (canonical1419 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node415 + (injectiveMoment H (mergeFirst pivotMatrix415 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix415 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix415 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix415 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value415, value132, value146, value149, value72, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation416 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem sound416 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node416 = Sparse.eval value416 (momentVector H) := by
  have heq : pivotMatrix416 = (fun u v => node416 (pivotPermutation416 u) v) := by apply Matrix.ext; unfold pivotMatrix416 node416 pivotPermutation416; decide +kernel
  have hmoment : injectiveMoment H node416 = injectiveMoment H pivotMatrix416 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix416 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix416 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix416 (0 : Fin 4)) =
      Sparse.eval value73 (momentVector H) := by
    have heq : mergeFirst pivotMatrix416 (0 : Fin 4) = raw236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix416 raw236; decide +kernel
    rw [heq]
    exact (canonical236 hH).trans (sound73 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix416 (1 : Fin 4)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix416 (1 : Fin 4) = raw1349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix416 raw1349; decide +kernel
    rw [heq]
    exact (canonical1349 hH).trans (sound132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix416 (2 : Fin 4)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix416 (2 : Fin 4) = raw1422 := by apply Matrix.ext; unfold mergeFirst pivotMatrix416 raw1422; decide +kernel
    rw [heq]
    exact (canonical1422 hH).trans (sound140 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix416 (3 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix416 (3 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix416 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node416 + (injectiveMoment H (mergeFirst pivotMatrix416 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix416 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix416 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix416 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value416, value132, value140, value153, value73, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation417 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix417 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem sound417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node417 = Sparse.eval value417 (momentVector H) := by
  have heq : pivotMatrix417 = (fun u v => node417 (pivotPermutation417 u) v) := by apply Matrix.ext; unfold pivotMatrix417 node417 pivotPermutation417; decide +kernel
  have hmoment : injectiveMoment H node417 = injectiveMoment H pivotMatrix417 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix417 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix417 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix417 (0 : Fin 4)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (0 : Fin 4) = raw239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw239; decide +kernel
    rw [heq]
    exact (canonical239 hH).trans (sound74 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix417 (1 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (1 : Fin 4) = raw1353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw1353; decide +kernel
    rw [heq]
    exact (canonical1353 hH).trans (sound134 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix417 (2 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (2 : Fin 4) = raw1426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw1426; decide +kernel
    rw [heq]
    exact (canonical1426 hH).trans (sound146 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix417 (3 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix417 (3 : Fin 4) = raw1434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix417 raw1434; decide +kernel
    rw [heq]
    exact (canonical1434 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node417 + (injectiveMoment H (mergeFirst pivotMatrix417 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix417 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix417 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix417 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value417, value134, value146, value153, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation418 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem sound418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node418 = Sparse.eval value418 (momentVector H) := by
  have heq : pivotMatrix418 = (fun u v => node418 (pivotPermutation418 u) v) := by apply Matrix.ext; unfold pivotMatrix418 node418 pivotPermutation418; decide +kernel
  have hmoment : injectiveMoment H node418 = injectiveMoment H pivotMatrix418 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix418 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix418 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix418 (0 : Fin 4)) =
      Sparse.eval value78 (momentVector H) := by
    have heq : mergeFirst pivotMatrix418 (0 : Fin 4) = raw248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix418 raw248; decide +kernel
    rw [heq]
    exact (canonical248 hH).trans (sound78 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix418 (1 : Fin 4)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix418 (1 : Fin 4) = raw1378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix418 raw1378; decide +kernel
    rw [heq]
    exact (canonical1378 hH).trans (sound144 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix418 (2 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix418 (2 : Fin 4) = raw1444 := by apply Matrix.ext; unfold mergeFirst pivotMatrix418 raw1444; decide +kernel
    rw [heq]
    exact (canonical1444 hH).trans (sound149 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix418 (3 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix418 (3 : Fin 4) = raw1445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix418 raw1445; decide +kernel
    rw [heq]
    exact (canonical1445 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node418 + (injectiveMoment H (mergeFirst pivotMatrix418 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix418 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix418 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix418 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value418, value144, value149, value153, value78, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation419 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem sound419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node419 = Sparse.eval value419 (momentVector H) := by
  have heq : pivotMatrix419 = (fun u v => node419 (pivotPermutation419 u) v) := by apply Matrix.ext; unfold pivotMatrix419 node419 pivotPermutation419; decide +kernel
  have hmoment : injectiveMoment H node419 = injectiveMoment H pivotMatrix419 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix419 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix419 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix419 (0 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix419 (0 : Fin 4) = raw297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix419 raw297; decide +kernel
    rw [heq]
    exact (canonical297 hH).trans (sound246 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix419 (1 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix419 (1 : Fin 4) = raw1353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix419 raw1353; decide +kernel
    rw [heq]
    exact (canonical1353 hH).trans (sound134 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix419 (2 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix419 (2 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix419 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix419 (3 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix419 (3 : Fin 4) = raw1418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix419 raw1418; decide +kernel
    rw [heq]
    exact (canonical1418 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node419 + (injectiveMoment H (mergeFirst pivotMatrix419 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix419 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix419 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix419 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value419, value134, value146, value150, value246, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation420 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix420 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem sound420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node420 = Sparse.eval value420 (momentVector H) := by
  have heq : pivotMatrix420 = (fun u v => node420 (pivotPermutation420 u) v) := by apply Matrix.ext; unfold pivotMatrix420 node420 pivotPermutation420; decide +kernel
  have hmoment : injectiveMoment H node420 = injectiveMoment H pivotMatrix420 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix420 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix420 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix420 (0 : Fin 4)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix420 (0 : Fin 4) = raw307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix420 raw307; decide +kernel
    rw [heq]
    exact (canonical307 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix420 (1 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix420 (1 : Fin 4) = raw1359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix420 raw1359; decide +kernel
    rw [heq]
    exact (canonical1359 hH).trans (sound102 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix420 (2 : Fin 4)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix420 (2 : Fin 4) = raw1423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix420 raw1423; decide +kernel
    rw [heq]
    exact (canonical1423 hH).trans (sound31 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix420 (3 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix420 (3 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix420 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node420 + (injectiveMoment H (mergeFirst pivotMatrix420 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix420 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix420 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix420 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value420, value102, value153, value201, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation421 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem sound421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node421 = Sparse.eval value421 (momentVector H) := by
  have heq : pivotMatrix421 = (fun u v => node421 (pivotPermutation421 u) v) := by apply Matrix.ext; unfold pivotMatrix421 node421 pivotPermutation421; decide +kernel
  have hmoment : injectiveMoment H node421 = injectiveMoment H pivotMatrix421 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix421 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix421 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix421 (0 : Fin 4)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix421 (0 : Fin 4) = raw309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix421 raw309; decide +kernel
    rw [heq]
    exact (canonical309 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix421 (1 : Fin 4)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix421 (1 : Fin 4) = raw1361 := by apply Matrix.ext; unfold mergeFirst pivotMatrix421 raw1361; decide +kernel
    rw [heq]
    exact (canonical1361 hH).trans (sound106 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix421 (2 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix421 (2 : Fin 4) = raw1426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix421 raw1426; decide +kernel
    rw [heq]
    exact (canonical1426 hH).trans (sound146 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix421 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix421 (3 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix421 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node421 + (injectiveMoment H (mergeFirst pivotMatrix421 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix421 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix421 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix421 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value421, value106, value145, value146, value206, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation422 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix422 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]

theorem sound422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node422 = Sparse.eval value422 (momentVector H) := by
  have heq : pivotMatrix422 = (fun u v => node422 (pivotPermutation422 u) v) := by apply Matrix.ext; unfold pivotMatrix422 node422 pivotPermutation422; decide +kernel
  have hmoment : injectiveMoment H node422 = injectiveMoment H pivotMatrix422 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix422 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix422 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix422 (0 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix422 (0 : Fin 4) = raw2692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix422 raw2692; decide +kernel
    rw [heq]
    exact (canonical2692 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix422 (1 : Fin 4)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix422 (1 : Fin 4) = raw1361 := by apply Matrix.ext; unfold mergeFirst pivotMatrix422 raw1361; decide +kernel
    rw [heq]
    exact (canonical1361 hH).trans (sound106 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix422 (2 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix422 (2 : Fin 4) = raw1353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix422 raw1353; decide +kernel
    rw [heq]
    exact (canonical1353 hH).trans (sound134 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix422 (3 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix422 (3 : Fin 4) = raw1351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix422 raw1351; decide +kernel
    rw [heq]
    exact (canonical1351 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node422 + (injectiveMoment H (mergeFirst pivotMatrix422 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix422 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix422 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix422 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value422, value106, value134, value146, value229, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation423 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix423 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -1, -1]]

theorem sound423 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node423 = Sparse.eval value423 (momentVector H) := by
  have heq : pivotMatrix423 = (fun u v => node423 (pivotPermutation423 u) v) := by apply Matrix.ext; unfold pivotMatrix423 node423 pivotPermutation423; decide +kernel
  have hmoment : injectiveMoment H node423 = injectiveMoment H pivotMatrix423 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix423 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix423 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix423 (0 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix423 (0 : Fin 4) = raw5497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix423 raw5497; decide +kernel
    rw [heq]
    exact (canonical5497 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix423 (1 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix423 (1 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix423 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix423 (2 : Fin 4)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix423 (2 : Fin 4) = raw1353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix423 raw1353; decide +kernel
    rw [heq]
    exact (canonical1353 hH).trans (sound134 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix423 (3 : Fin 4)) =
      Sparse.eval value112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix423 (3 : Fin 4) = raw1346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix423 raw1346; decide +kernel
    rw [heq]
    exact (canonical1346 hH).trans (sound112 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node423 + (injectiveMoment H (mergeFirst pivotMatrix423 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix423 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix423 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix423 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value423, value112, value134, value146, value225, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation424 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix424 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0]]

theorem sound424 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node424 = Sparse.eval value424 (momentVector H) := by
  have heq : pivotMatrix424 = (fun u v => node424 (pivotPermutation424 u) v) := by apply Matrix.ext; unfold pivotMatrix424 node424 pivotPermutation424; decide +kernel
  have hmoment : injectiveMoment H node424 = injectiveMoment H pivotMatrix424 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix424 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix424 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix424 (0 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix424 (0 : Fin 4) = raw5886 := by apply Matrix.ext; unfold mergeFirst pivotMatrix424 raw5886; decide +kernel
    rw [heq]
    exact (canonical5886 hH).trans (sound212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix424 (1 : Fin 4)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix424 (1 : Fin 4) = raw1428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix424 raw1428; decide +kernel
    rw [heq]
    exact (canonical1428 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix424 (2 : Fin 4)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix424 (2 : Fin 4) = raw1354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix424 raw1354; decide +kernel
    rw [heq]
    exact (canonical1354 hH).trans (sound135 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix424 (3 : Fin 4)) =
      Sparse.eval value112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix424 (3 : Fin 4) = raw1346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix424 raw1346; decide +kernel
    rw [heq]
    exact (canonical1346 hH).trans (sound112 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node424 + (injectiveMoment H (mergeFirst pivotMatrix424 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix424 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix424 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix424 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value424, value112, value135, value151, value212, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation425 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix425 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound425 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node425 = Sparse.eval value425 (momentVector H) := by
  have heq : pivotMatrix425 = (fun u v => node425 (pivotPermutation425 u) v) := by apply Matrix.ext; unfold pivotMatrix425 node425 pivotPermutation425; decide +kernel
  have hmoment : injectiveMoment H node425 = injectiveMoment H pivotMatrix425 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix425 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix425 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix425 (0 : Fin 4)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix425 (0 : Fin 4) = raw5498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix425 raw5498; decide +kernel
    rw [heq]
    exact (canonical5498 hH).trans (sound245 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix425 (1 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix425 (1 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix425 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix425 (2 : Fin 4)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix425 (2 : Fin 4) = raw1355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix425 raw1355; decide +kernel
    rw [heq]
    exact (canonical1355 hH).trans (sound135 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix425 (3 : Fin 4)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix425 (3 : Fin 4) = raw1349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix425 raw1349; decide +kernel
    rw [heq]
    exact (canonical1349 hH).trans (sound132 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node425 + (injectiveMoment H (mergeFirst pivotMatrix425 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix425 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix425 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix425 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value425, value132, value135, value149, value245, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation426 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix426 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]

theorem sound426 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node426 = Sparse.eval value426 (momentVector H) := by
  have heq : pivotMatrix426 = (fun u v => node426 (pivotPermutation426 u) v) := by apply Matrix.ext; unfold pivotMatrix426 node426 pivotPermutation426; decide +kernel
  have hmoment : injectiveMoment H node426 = injectiveMoment H pivotMatrix426 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix426 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix426 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix426 (0 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix426 (0 : Fin 4) = raw2701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix426 raw2701; decide +kernel
    rw [heq]
    exact (canonical2701 hH).trans (sound109 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix426 (1 : Fin 4)) =
      Sparse.eval value137 (momentVector H) := by
    have heq : mergeFirst pivotMatrix426 (1 : Fin 4) = raw1364 := by apply Matrix.ext; unfold mergeFirst pivotMatrix426 raw1364; decide +kernel
    rw [heq]
    exact (canonical1364 hH).trans (sound137 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix426 (2 : Fin 4)) =
      Sparse.eval value106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix426 (2 : Fin 4) = raw1361 := by apply Matrix.ext; unfold mergeFirst pivotMatrix426 raw1361; decide +kernel
    rw [heq]
    exact (canonical1361 hH).trans (sound106 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix426 (3 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix426 (3 : Fin 4) = raw1359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix426 raw1359; decide +kernel
    rw [heq]
    exact (canonical1359 hH).trans (sound102 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node426 + (injectiveMoment H (mergeFirst pivotMatrix426 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix426 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix426 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix426 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value426, value102, value106, value109, value137, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation427 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix427 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node427 = Sparse.eval value427 (momentVector H) := by
  have heq : pivotMatrix427 = (fun u v => node427 (pivotPermutation427 u) v) := by apply Matrix.ext; unfold pivotMatrix427 node427 pivotPermutation427; decide +kernel
  have hmoment : injectiveMoment H node427 = injectiveMoment H pivotMatrix427 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix427 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix427 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix427 (0 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix427 (0 : Fin 4) = raw5505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix427 raw5505; decide +kernel
    rw [heq]
    exact (canonical5505 hH).trans (sound247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix427 (1 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix427 (1 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix427 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix427 (2 : Fin 4)) =
      Sparse.eval value136 (momentVector H) := by
    have heq : mergeFirst pivotMatrix427 (2 : Fin 4) = raw1362 := by apply Matrix.ext; unfold mergeFirst pivotMatrix427 raw1362; decide +kernel
    rw [heq]
    exact (canonical1362 hH).trans (sound136 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix427 (3 : Fin 4)) =
      Sparse.eval value102 (momentVector H) := by
    have heq : mergeFirst pivotMatrix427 (3 : Fin 4) = raw1359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix427 raw1359; decide +kernel
    rw [heq]
    exact (canonical1359 hH).trans (sound102 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node427 + (injectiveMoment H (mergeFirst pivotMatrix427 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix427 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix427 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix427 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value427, value102, value136, value153, value247, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation428 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix428 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound428 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node428 = Sparse.eval value428 (momentVector H) := by
  have heq : pivotMatrix428 = (fun u v => node428 (pivotPermutation428 u) v) := by apply Matrix.ext; unfold pivotMatrix428 node428 pivotPermutation428; decide +kernel
  have hmoment : injectiveMoment H node428 = injectiveMoment H pivotMatrix428 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix428 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix428 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix428 (0 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix428 (0 : Fin 4) = raw5509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix428 raw5509; decide +kernel
    rw [heq]
    exact (canonical5509 hH).trans (sound249 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix428 (1 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix428 (1 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix428 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix428 (2 : Fin 4)) =
      Sparse.eval value138 (momentVector H) := by
    have heq : mergeFirst pivotMatrix428 (2 : Fin 4) = raw1365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix428 raw1365; decide +kernel
    rw [heq]
    exact (canonical1365 hH).trans (sound138 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix428 (3 : Fin 4)) =
      Sparse.eval value137 (momentVector H) := by
    have heq : mergeFirst pivotMatrix428 (3 : Fin 4) = raw1364 := by apply Matrix.ext; unfold mergeFirst pivotMatrix428 raw1364; decide +kernel
    rw [heq]
    exact (canonical1364 hH).trans (sound137 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node428 + (injectiveMoment H (mergeFirst pivotMatrix428 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix428 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix428 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix428 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value428, value137, value138, value155, value249, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation429 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix429 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem sound429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node429 = Sparse.eval value429 (momentVector H) := by
  have heq : pivotMatrix429 = (fun u v => node429 (pivotPermutation429 u) v) := by apply Matrix.ext; unfold pivotMatrix429 node429 pivotPermutation429; decide +kernel
  have hmoment : injectiveMoment H node429 = injectiveMoment H pivotMatrix429 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix429 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix429 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix429 (0 : Fin 4)) =
      Sparse.eval value119 (momentVector H) := by
    have heq : mergeFirst pivotMatrix429 (0 : Fin 4) = raw936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix429 raw936; decide +kernel
    rw [heq]
    exact (canonical936 hH).trans (sound119 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix429 (1 : Fin 4)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix429 (1 : Fin 4) = raw1382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix429 raw1382; decide +kernel
    rw [heq]
    exact (canonical1382 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix429 (2 : Fin 4)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix429 (2 : Fin 4) = raw1396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix429 raw1396; decide +kernel
    rw [heq]
    exact (canonical1396 hH).trans (sound52 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix429 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix429 (3 : Fin 4) = raw1403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix429 raw1403; decide +kernel
    rw [heq]
    exact (canonical1403 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node429 + (injectiveMoment H (mergeFirst pivotMatrix429 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix429 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix429 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix429 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value429, value119, value145, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation430 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix430 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem sound430 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node430 = Sparse.eval value430 (momentVector H) := by
  have heq : pivotMatrix430 = (fun u v => node430 (pivotPermutation430 u) v) := by apply Matrix.ext; unfold pivotMatrix430 node430 pivotPermutation430; decide +kernel
  have hmoment : injectiveMoment H node430 = injectiveMoment H pivotMatrix430 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix430 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix430 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix430 (0 : Fin 4)) =
      Sparse.eval value120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (0 : Fin 4) = raw940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw940; decide +kernel
    rw [heq]
    exact (canonical940 hH).trans (sound120 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix430 (1 : Fin 4)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (1 : Fin 4) = raw1384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw1384; decide +kernel
    rw [heq]
    exact (canonical1384 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix430 (2 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (2 : Fin 4) = raw1403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw1403; decide +kernel
    rw [heq]
    exact (canonical1403 hH).trans (sound145 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix430 (3 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix430 (3 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix430 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node430 + (injectiveMoment H (mergeFirst pivotMatrix430 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix430 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix430 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix430 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value430, value120, value145, value146, value31, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation431 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix431 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem sound431 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node431 = Sparse.eval value431 (momentVector H) := by
  have heq : pivotMatrix431 = (fun u v => node431 (pivotPermutation431 u) v) := by apply Matrix.ext; unfold pivotMatrix431 node431 pivotPermutation431; decide +kernel
  have hmoment : injectiveMoment H node431 = injectiveMoment H pivotMatrix431 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix431 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix431 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix431 (0 : Fin 4)) =
      Sparse.eval value122 (momentVector H) := by
    have heq : mergeFirst pivotMatrix431 (0 : Fin 4) = raw943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix431 raw943; decide +kernel
    rw [heq]
    exact (canonical943 hH).trans (sound122 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix431 (1 : Fin 4)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix431 (1 : Fin 4) = raw1386 := by apply Matrix.ext; unfold mergeFirst pivotMatrix431 raw1386; decide +kernel
    rw [heq]
    exact (canonical1386 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix431 (2 : Fin 4)) =
      Sparse.eval value148 (momentVector H) := by
    have heq : mergeFirst pivotMatrix431 (2 : Fin 4) = raw1413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix431 raw1413; decide +kernel
    rw [heq]
    exact (canonical1413 hH).trans (sound148 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix431 (3 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix431 (3 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix431 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node431 + (injectiveMoment H (mergeFirst pivotMatrix431 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix431 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix431 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix431 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value431, value122, value148, value149, value59, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation432 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix432 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem sound432 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node432 = Sparse.eval value432 (momentVector H) := by
  have heq : pivotMatrix432 = (fun u v => node432 (pivotPermutation432 u) v) := by apply Matrix.ext; unfold pivotMatrix432 node432 pivotPermutation432; decide +kernel
  have hmoment : injectiveMoment H node432 = injectiveMoment H pivotMatrix432 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix432 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix432 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix432 (0 : Fin 4)) =
      Sparse.eval value123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix432 (0 : Fin 4) = raw944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix432 raw944; decide +kernel
    rw [heq]
    exact (canonical944 hH).trans (sound123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix432 (1 : Fin 4)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix432 (1 : Fin 4) = raw1387 := by apply Matrix.ext; unfold mergeFirst pivotMatrix432 raw1387; decide +kernel
    rw [heq]
    exact (canonical1387 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix432 (2 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix432 (2 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix432 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix432 (3 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix432 (3 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix432 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node432 + (injectiveMoment H (mergeFirst pivotMatrix432 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix432 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix432 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix432 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value432, value123, value149, value150, value52, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation433 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix433 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem sound433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node433 = Sparse.eval value433 (momentVector H) := by
  have heq : pivotMatrix433 = (fun u v => node433 (pivotPermutation433 u) v) := by apply Matrix.ext; unfold pivotMatrix433 node433 pivotPermutation433; decide +kernel
  have hmoment : injectiveMoment H node433 = injectiveMoment H pivotMatrix433 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix433 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix433 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix433 (0 : Fin 4)) =
      Sparse.eval value124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix433 (0 : Fin 4) = raw945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix433 raw945; decide +kernel
    rw [heq]
    exact (canonical945 hH).trans (sound124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix433 (1 : Fin 4)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix433 (1 : Fin 4) = raw1388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix433 raw1388; decide +kernel
    rw [heq]
    exact (canonical1388 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix433 (2 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix433 (2 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix433 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix433 (3 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix433 (3 : Fin 4) = raw1418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix433 raw1418; decide +kernel
    rw [heq]
    exact (canonical1418 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node433 + (injectiveMoment H (mergeFirst pivotMatrix433 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix433 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix433 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix433 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value433, value124, value150, value35, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation434 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix434 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound434 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node434 = Sparse.eval value434 (momentVector H) := by
  have heq : pivotMatrix434 = (fun u v => node434 (pivotPermutation434 u) v) := by apply Matrix.ext; unfold pivotMatrix434 node434 pivotPermutation434; decide +kernel
  have hmoment : injectiveMoment H node434 = injectiveMoment H pivotMatrix434 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix434 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix434 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix434 (0 : Fin 4)) =
      Sparse.eval value127 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (0 : Fin 4) = raw953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw953; decide +kernel
    rw [heq]
    exact (canonical953 hH).trans (sound127 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix434 (1 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (1 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix434 (2 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (2 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix434 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix434 (3 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix434 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node434 + (injectiveMoment H (mergeFirst pivotMatrix434 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix434 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix434 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix434 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value434, value127, value145, value150, value153, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation435 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix435 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound435 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node435 = Sparse.eval value435 (momentVector H) := by
  have heq : pivotMatrix435 = (fun u v => node435 (pivotPermutation435 u) v) := by apply Matrix.ext; unfold pivotMatrix435 node435 pivotPermutation435; decide +kernel
  have hmoment : injectiveMoment H node435 = injectiveMoment H pivotMatrix435 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix435 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix435 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix435 (0 : Fin 4)) =
      Sparse.eval value129 (momentVector H) := by
    have heq : mergeFirst pivotMatrix435 (0 : Fin 4) = raw957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix435 raw957; decide +kernel
    rw [heq]
    exact (canonical957 hH).trans (sound129 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix435 (1 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix435 (1 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix435 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix435 (2 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix435 (2 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix435 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix435 (3 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix435 (3 : Fin 4) = raw1438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix435 raw1438; decide +kernel
    rw [heq]
    exact (canonical1438 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node435 + (injectiveMoment H (mergeFirst pivotMatrix435 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix435 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix435 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix435 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value435, value129, value145, value155, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation436 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix436 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem sound436 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node436 = Sparse.eval value436 (momentVector H) := by
  have heq : pivotMatrix436 = (fun u v => node436 (pivotPermutation436 u) v) := by apply Matrix.ext; unfold pivotMatrix436 node436 pivotPermutation436; decide +kernel
  have hmoment : injectiveMoment H node436 = injectiveMoment H pivotMatrix436 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix436 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix436 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix436 (0 : Fin 4)) =
      Sparse.eval value130 (momentVector H) := by
    have heq : mergeFirst pivotMatrix436 (0 : Fin 4) = raw959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix436 raw959; decide +kernel
    rw [heq]
    exact (canonical959 hH).trans (sound130 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix436 (1 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix436 (1 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix436 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix436 (2 : Fin 4)) =
      Sparse.eval value156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix436 (2 : Fin 4) = raw1440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix436 raw1440; decide +kernel
    rw [heq]
    exact (canonical1440 hH).trans (sound156 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix436 (3 : Fin 4)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix436 (3 : Fin 4) = raw1441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix436 raw1441; decide +kernel
    rw [heq]
    exact (canonical1441 hH).trans (sound157 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node436 + (injectiveMoment H (mergeFirst pivotMatrix436 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix436 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix436 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix436 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value436, value130, value155, value156, value157, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation437 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix437 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem sound437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node437 = Sparse.eval value437 (momentVector H) := by
  have heq : pivotMatrix437 = (fun u v => node437 (pivotPermutation437 u) v) := by apply Matrix.ext; unfold pivotMatrix437 node437 pivotPermutation437; decide +kernel
  have hmoment : injectiveMoment H node437 = injectiveMoment H pivotMatrix437 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix437 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix437 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix437 (0 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix437 (0 : Fin 4) = raw2803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix437 raw2803; decide +kernel
    rw [heq]
    exact (canonical2803 hH).trans (sound176 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix437 (1 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix437 (1 : Fin 4) = raw1426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix437 raw1426; decide +kernel
    rw [heq]
    exact (canonical1426 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix437 (2 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix437 (2 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix437 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix437 (3 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix437 (3 : Fin 4) = raw1403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix437 raw1403; decide +kernel
    rw [heq]
    exact (canonical1403 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node437 + (injectiveMoment H (mergeFirst pivotMatrix437 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix437 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix437 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix437 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value437, value145, value146, value176, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation438 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix438 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem sound438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node438 = Sparse.eval value438 (momentVector H) := by
  have heq : pivotMatrix438 = (fun u v => node438 (pivotPermutation438 u) v) := by apply Matrix.ext; unfold pivotMatrix438 node438 pivotPermutation438; decide +kernel
  have hmoment : injectiveMoment H node438 = injectiveMoment H pivotMatrix438 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix438 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix438 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix438 (0 : Fin 4)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix438 (0 : Fin 4) = raw2811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix438 raw2811; decide +kernel
    rw [heq]
    exact (canonical2811 hH).trans (sound177 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix438 (1 : Fin 4)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix438 (1 : Fin 4) = raw1428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix438 raw1428; decide +kernel
    rw [heq]
    exact (canonical1428 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix438 (2 : Fin 4)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix438 (2 : Fin 4) = raw1412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix438 raw1412; decide +kernel
    rw [heq]
    exact (canonical1412 hH).trans (sound147 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix438 (3 : Fin 4)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix438 (3 : Fin 4) = raw1409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix438 raw1409; decide +kernel
    rw [heq]
    exact (canonical1409 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node438 + (injectiveMoment H (mergeFirst pivotMatrix438 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix438 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix438 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix438 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value438, value146, value147, value151, value177, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation439 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix439 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem sound439 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node439 = Sparse.eval value439 (momentVector H) := by
  have heq : pivotMatrix439 = (fun u v => node439 (pivotPermutation439 u) v) := by apply Matrix.ext; unfold pivotMatrix439 node439 pivotPermutation439; decide +kernel
  have hmoment : injectiveMoment H node439 = injectiveMoment H pivotMatrix439 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix439 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix439 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix439 (0 : Fin 4)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix439 (0 : Fin 4) = raw2817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix439 raw2817; decide +kernel
    rw [heq]
    exact (canonical2817 hH).trans (sound180 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix439 (1 : Fin 4)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix439 (1 : Fin 4) = raw1429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix439 raw1429; decide +kernel
    rw [heq]
    exact (canonical1429 hH).trans (sound152 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix439 (2 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix439 (2 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix439 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix439 (3 : Fin 4)) =
      Sparse.eval value148 (momentVector H) := by
    have heq : mergeFirst pivotMatrix439 (3 : Fin 4) = raw1413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix439 raw1413; decide +kernel
    rw [heq]
    exact (canonical1413 hH).trans (sound148 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node439 + (injectiveMoment H (mergeFirst pivotMatrix439 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix439 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix439 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix439 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value439, value148, value149, value152, value180, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation440 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix440 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound440 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node440 = Sparse.eval value440 (momentVector H) := by
  have heq : pivotMatrix440 = (fun u v => node440 (pivotPermutation440 u) v) := by apply Matrix.ext; unfold pivotMatrix440 node440 pivotPermutation440; decide +kernel
  have hmoment : injectiveMoment H node440 = injectiveMoment H pivotMatrix440 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix440 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix440 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix440 (0 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix440 (0 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix440 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix440 (1 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix440 (1 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix440 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix440 (2 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix440 (2 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix440 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix440 (3 : Fin 4)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix440 (3 : Fin 4) = raw1416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix440 raw1416; decide +kernel
    rw [heq]
    exact (canonical1416 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node440 + (injectiveMoment H (mergeFirst pivotMatrix440 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix440 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix440 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix440 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value440, value149, value150, value153, value181, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation441 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix441 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node441 = Sparse.eval value441 (momentVector H) := by
  have heq : pivotMatrix441 = (fun u v => node441 (pivotPermutation441 u) v) := by apply Matrix.ext; unfold pivotMatrix441 node441 pivotPermutation441; decide +kernel
  have hmoment : injectiveMoment H node441 = injectiveMoment H pivotMatrix441 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix441 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix441 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix441 (0 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix441 (0 : Fin 4) = raw2821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix441 raw2821; decide +kernel
    rw [heq]
    exact (canonical2821 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix441 (1 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix441 (1 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix441 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix441 (2 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix441 (2 : Fin 4) = raw1418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix441 raw1418; decide +kernel
    rw [heq]
    exact (canonical1418 hH).trans (sound150 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix441 (3 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix441 (3 : Fin 4) = raw1417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix441 raw1417; decide +kernel
    rw [heq]
    exact (canonical1417 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node441 + (injectiveMoment H (mergeFirst pivotMatrix441 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix441 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix441 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix441 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value441, value145, value150, value271, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation442 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix442 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem sound442 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node442 = Sparse.eval value442 (momentVector H) := by
  have heq : pivotMatrix442 = (fun u v => node442 (pivotPermutation442 u) v) := by apply Matrix.ext; unfold pivotMatrix442 node442 pivotPermutation442; decide +kernel
  have hmoment : injectiveMoment H node442 = injectiveMoment H pivotMatrix442 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix442 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix442 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix442 (0 : Fin 4)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix442 (0 : Fin 4) = raw2839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix442 raw2839; decide +kernel
    rw [heq]
    exact (canonical2839 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix442 (1 : Fin 4)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix442 (1 : Fin 4) = raw1436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix442 raw1436; decide +kernel
    rw [heq]
    exact (canonical1436 hH).trans (sound154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix442 (2 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix442 (2 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix442 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix442 (3 : Fin 4)) =
      Sparse.eval value152 (momentVector H) := by
    have heq : mergeFirst pivotMatrix442 (3 : Fin 4) = raw1429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix442 raw1429; decide +kernel
    rw [heq]
    exact (canonical1429 hH).trans (sound152 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node442 + (injectiveMoment H (mergeFirst pivotMatrix442 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix442 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix442 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix442 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value442, value152, value153, value154, value184, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation443 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix443 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node443 = Sparse.eval value443 (momentVector H) := by
  have heq : pivotMatrix443 = (fun u v => node443 (pivotPermutation443 u) v) := by apply Matrix.ext; unfold pivotMatrix443 node443 pivotPermutation443; decide +kernel
  have hmoment : injectiveMoment H node443 = injectiveMoment H pivotMatrix443 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix443 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix443 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix443 (0 : Fin 4)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix443 (0 : Fin 4) = raw2842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix443 raw2842; decide +kernel
    rw [heq]
    exact (canonical2842 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix443 (1 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix443 (1 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix443 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix443 (2 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix443 (2 : Fin 4) = raw1433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix443 raw1433; decide +kernel
    rw [heq]
    exact (canonical1433 hH).trans (sound145 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix443 (3 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix443 (3 : Fin 4) = raw1432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix443 raw1432; decide +kernel
    rw [heq]
    exact (canonical1432 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node443 + (injectiveMoment H (mergeFirst pivotMatrix443 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix443 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix443 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix443 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value443, value145, value153, value155, value185, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation444 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix444 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem sound444 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node444 = Sparse.eval value444 (momentVector H) := by
  have heq : pivotMatrix444 = (fun u v => node444 (pivotPermutation444 u) v) := by apply Matrix.ext; unfold pivotMatrix444 node444 pivotPermutation444; decide +kernel
  have hmoment : injectiveMoment H node444 = injectiveMoment H pivotMatrix444 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix444 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix444 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix444 (0 : Fin 4)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix444 (0 : Fin 4) = raw2847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix444 raw2847; decide +kernel
    rw [heq]
    exact (canonical2847 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix444 (1 : Fin 4)) =
      Sparse.eval value156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix444 (1 : Fin 4) = raw1440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix444 raw1440; decide +kernel
    rw [heq]
    exact (canonical1440 hH).trans (sound156 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix444 (2 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix444 (2 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix444 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix444 (3 : Fin 4)) =
      Sparse.eval value154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix444 (3 : Fin 4) = raw1436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix444 raw1436; decide +kernel
    rw [heq]
    exact (canonical1436 hH).trans (sound154 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node444 + (injectiveMoment H (mergeFirst pivotMatrix444 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix444 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix444 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix444 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value444, value154, value155, value156, value187, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation445 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix445 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem sound445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node445 = Sparse.eval value445 (momentVector H) := by
  have heq : pivotMatrix445 = (fun u v => node445 (pivotPermutation445 u) v) := by apply Matrix.ext; unfold pivotMatrix445 node445 pivotPermutation445; decide +kernel
  have hmoment : injectiveMoment H node445 = injectiveMoment H pivotMatrix445 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix445 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix445 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix445 (0 : Fin 4)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (0 : Fin 4) = raw2848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw2848; decide +kernel
    rw [heq]
    exact (canonical2848 hH).trans (sound188 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix445 (1 : Fin 4)) =
      Sparse.eval value157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (1 : Fin 4) = raw1441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw1441; decide +kernel
    rw [heq]
    exact (canonical1441 hH).trans (sound157 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix445 (2 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (2 : Fin 4) = raw1438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw1438; decide +kernel
    rw [heq]
    exact (canonical1438 hH).trans (sound155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix445 (3 : Fin 4)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix445 (3 : Fin 4) = raw1437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix445 raw1437; decide +kernel
    rw [heq]
    exact (canonical1437 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node445 + (injectiveMoment H (mergeFirst pivotMatrix445 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix445 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix445 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix445 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value445, value155, value157, value188, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation446 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix446 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

theorem sound446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node446 = Sparse.eval value446 (momentVector H) := by
  have heq : pivotMatrix446 = (fun u v => node446 (pivotPermutation446 u) v) := by apply Matrix.ext; unfold pivotMatrix446 node446 pivotPermutation446; decide +kernel
  have hmoment : injectiveMoment H node446 = injectiveMoment H pivotMatrix446 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix446 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix446 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix446 (0 : Fin 4)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix446 (0 : Fin 4) = raw5544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix446 raw5544; decide +kernel
    rw [heq]
    exact (canonical5544 hH).trans (sound256 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix446 (1 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix446 (1 : Fin 4) = raw1448 := by apply Matrix.ext; unfold mergeFirst pivotMatrix446 raw1448; decide +kernel
    rw [heq]
    exact (canonical1448 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix446 (2 : Fin 4)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix446 (2 : Fin 4) = raw1434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix446 raw1434; decide +kernel
    rw [heq]
    exact (canonical1434 hH).trans (sound153 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix446 (3 : Fin 4)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix446 (3 : Fin 4) = raw1428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix446 raw1428; decide +kernel
    rw [heq]
    exact (canonical1428 hH).trans (sound151 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node446 + (injectiveMoment H (mergeFirst pivotMatrix446 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix446 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix446 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix446 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value446, value151, value153, value256, Sparse.eval] at hc ⊢
  linarith

theorem sound447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node447 = Sparse.eval value447 (momentVector H) := by
  have hc : momentVector H 311 = injectiveMoment H node447 := rfl
  simp [value447, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
