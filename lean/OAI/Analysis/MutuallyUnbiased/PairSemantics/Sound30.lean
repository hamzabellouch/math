import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical99
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical100
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical134
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical135
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1920 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1920 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound1920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1920 = Sparse.eval value1920 (momentVector H) := by
  have heq : pivotMatrix1920 = (fun u v => node1920 (pivotPermutation1920 u) v) := by apply Matrix.ext; unfold pivotMatrix1920 node1920 pivotPermutation1920; decide +kernel
  have hmoment : injectiveMoment H node1920 = injectiveMoment H pivotMatrix1920 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1920 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1920 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1920 (0 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (0 : Fin 4) = raw3200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw3200; decide +kernel
    rw [heq]
    exact (canonical3200 hH).trans (sound1052 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1920 (1 : Fin 4)) =
      Sparse.eval value912 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (1 : Fin 4) = raw3008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw3008; decide +kernel
    rw [heq]
    exact (canonical3008 hH).trans (sound912 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1920 (2 : Fin 4)) =
      Sparse.eval value1055 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (2 : Fin 4) = raw2998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw2998; decide +kernel
    rw [heq]
    exact (canonical2998 hH).trans (sound1055 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1920 (3 : Fin 4)) =
      Sparse.eval value1051 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1920 (3 : Fin 4) = raw2996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1920 raw2996; decide +kernel
    rw [heq]
    exact (canonical2996 hH).trans (sound1051 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1920 + (injectiveMoment H (mergeFirst pivotMatrix1920 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1920 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1920 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1920 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1920, value1051, value1052, value1055, value912, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1921 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1921 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

theorem sound1921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1921 = Sparse.eval value1921 (momentVector H) := by
  have heq : pivotMatrix1921 = (fun u v => node1921 (pivotPermutation1921 u) v) := by apply Matrix.ext; unfold pivotMatrix1921 node1921 pivotPermutation1921; decide +kernel
  have hmoment : injectiveMoment H node1921 = injectiveMoment H pivotMatrix1921 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1921 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1921 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1921 (0 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (0 : Fin 4) = raw3204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw3204; decide +kernel
    rw [heq]
    exact (canonical3204 hH).trans (sound1056 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1921 (1 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (1 : Fin 4) = raw3009 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw3009; decide +kernel
    rw [heq]
    exact (canonical3009 hH).trans (sound772 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1921 (2 : Fin 4)) =
      Sparse.eval value1159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (2 : Fin 4) = raw3001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw3001; decide +kernel
    rw [heq]
    exact (canonical3001 hH).trans (sound1159 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1921 (3 : Fin 4)) =
      Sparse.eval value1055 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1921 (3 : Fin 4) = raw2998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1921 raw2998; decide +kernel
    rw [heq]
    exact (canonical2998 hH).trans (sound1055 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1921 + (injectiveMoment H (mergeFirst pivotMatrix1921 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1921 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1921 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1921 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1921, value1055, value1056, value1159, value772, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1922 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1922 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

theorem sound1922 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1922 = Sparse.eval value1922 (momentVector H) := by
  have heq : pivotMatrix1922 = (fun u v => node1922 (pivotPermutation1922 u) v) := by apply Matrix.ext; unfold pivotMatrix1922 node1922 pivotPermutation1922; decide +kernel
  have hmoment : injectiveMoment H node1922 = injectiveMoment H pivotMatrix1922 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1922 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1922 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1922 (0 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (0 : Fin 4) = raw3208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3208; decide +kernel
    rw [heq]
    exact (canonical3208 hH).trans (sound1269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1922 (1 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (1 : Fin 4) = raw3011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3011; decide +kernel
    rw [heq]
    exact (canonical3011 hH).trans (sound1180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1922 (2 : Fin 4)) =
      Sparse.eval value1229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (2 : Fin 4) = raw3003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3003; decide +kernel
    rw [heq]
    exact (canonical3003 hH).trans (sound1229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1922 (3 : Fin 4)) =
      Sparse.eval value1159 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1922 (3 : Fin 4) = raw3001 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1922 raw3001; decide +kernel
    rw [heq]
    exact (canonical3001 hH).trans (sound1159 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1922 + (injectiveMoment H (mergeFirst pivotMatrix1922 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1922 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1922 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1922 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1922, value1159, value1180, value1229, value1269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1923 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1923 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

theorem sound1923 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1923 = Sparse.eval value1923 (momentVector H) := by
  have heq : pivotMatrix1923 = (fun u v => node1923 (pivotPermutation1923 u) v) := by apply Matrix.ext; unfold pivotMatrix1923 node1923 pivotPermutation1923; decide +kernel
  have hmoment : injectiveMoment H node1923 = injectiveMoment H pivotMatrix1923 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1923 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1923 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1923 (0 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1923 (0 : Fin 4) = raw3232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1923 raw3232; decide +kernel
    rw [heq]
    exact (canonical3232 hH).trans (sound943 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1923 (1 : Fin 4)) =
      Sparse.eval value465 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1923 (1 : Fin 4) = raw3023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1923 raw3023; decide +kernel
    rw [heq]
    exact (canonical3023 hH).trans (sound465 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1923 (2 : Fin 4)) =
      Sparse.eval value900 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1923 (2 : Fin 4) = raw3013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1923 raw3013; decide +kernel
    rw [heq]
    exact (canonical3013 hH).trans (sound900 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1923 (3 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1923 (3 : Fin 4) = raw3012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1923 raw3012; decide +kernel
    rw [heq]
    exact (canonical3012 hH).trans (sound772 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1923 + (injectiveMoment H (mergeFirst pivotMatrix1923 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1923 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1923 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1923 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1923, value465, value772, value900, value943, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1924 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1924 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem sound1924 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1924 = Sparse.eval value1924 (momentVector H) := by
  have heq : pivotMatrix1924 = (fun u v => node1924 (pivotPermutation1924 u) v) := by apply Matrix.ext; unfold pivotMatrix1924 node1924 pivotPermutation1924; decide +kernel
  have hmoment : injectiveMoment H node1924 = injectiveMoment H pivotMatrix1924 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1924 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1924 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1924 (0 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1924 (0 : Fin 4) = raw3241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1924 raw3241; decide +kernel
    rw [heq]
    exact (canonical3241 hH).trans (sound490 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1924 (1 : Fin 4)) =
      Sparse.eval value583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1924 (1 : Fin 4) = raw3027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1924 raw3027; decide +kernel
    rw [heq]
    exact (canonical3027 hH).trans (sound583 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1924 (2 : Fin 4)) =
      Sparse.eval value465 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1924 (2 : Fin 4) = raw3023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1924 raw3023; decide +kernel
    rw [heq]
    exact (canonical3023 hH).trans (sound465 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1924 (3 : Fin 4)) =
      Sparse.eval value404 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1924 (3 : Fin 4) = raw3022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1924 raw3022; decide +kernel
    rw [heq]
    exact (canonical3022 hH).trans (sound404 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1924 + (injectiveMoment H (mergeFirst pivotMatrix1924 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1924 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1924 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1924 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1924, value404, value465, value490, value583, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1925 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1925 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

theorem sound1925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1925 = Sparse.eval value1925 (momentVector H) := by
  have heq : pivotMatrix1925 = (fun u v => node1925 (pivotPermutation1925 u) v) := by apply Matrix.ext; unfold pivotMatrix1925 node1925 pivotPermutation1925; decide +kernel
  have hmoment : injectiveMoment H node1925 = injectiveMoment H pivotMatrix1925 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1925 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1925 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1925 (0 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1925 (0 : Fin 4) = raw3264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1925 raw3264; decide +kernel
    rw [heq]
    exact (canonical3264 hH).trans (sound476 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1925 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1925 (1 : Fin 4) = raw3039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1925 raw3039; decide +kernel
    rw [heq]
    exact (canonical3039 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1925 (2 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1925 (2 : Fin 4) = raw3034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1925 raw3034; decide +kernel
    rw [heq]
    exact (canonical3034 hH).trans (sound469 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1925 (3 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1925 (3 : Fin 4) = raw3033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1925 raw3033; decide +kernel
    rw [heq]
    exact (canonical3033 hH).trans (sound584 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1925 + (injectiveMoment H (mergeFirst pivotMatrix1925 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1925 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1925 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1925 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1925, value397, value469, value476, value584, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1926 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1926 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem sound1926 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1926 = Sparse.eval value1926 (momentVector H) := by
  have heq : pivotMatrix1926 = (fun u v => node1926 (pivotPermutation1926 u) v) := by apply Matrix.ext; unfold pivotMatrix1926 node1926 pivotPermutation1926; decide +kernel
  have hmoment : injectiveMoment H node1926 = injectiveMoment H pivotMatrix1926 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1926 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1926 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1926 (0 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1926 (0 : Fin 4) = raw3265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1926 raw3265; decide +kernel
    rw [heq]
    exact (canonical3265 hH).trans (sound944 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1926 (1 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1926 (1 : Fin 4) = raw3040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1926 raw3040; decide +kernel
    rw [heq]
    exact (canonical3040 hH).trans (sound773 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1926 (2 : Fin 4)) =
      Sparse.eval value901 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1926 (2 : Fin 4) = raw3035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1926 raw3035; decide +kernel
    rw [heq]
    exact (canonical3035 hH).trans (sound901 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1926 (3 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1926 (3 : Fin 4) = raw3034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1926 raw3034; decide +kernel
    rw [heq]
    exact (canonical3034 hH).trans (sound469 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1926 + (injectiveMoment H (mergeFirst pivotMatrix1926 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1926 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1926 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1926 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1926, value469, value773, value901, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1927 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1927 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound1927 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1927 = Sparse.eval value1927 (momentVector H) := by
  have heq : pivotMatrix1927 = (fun u v => node1927 (pivotPermutation1927 u) v) := by apply Matrix.ext; unfold pivotMatrix1927 node1927 pivotPermutation1927; decide +kernel
  have hmoment : injectiveMoment H node1927 = injectiveMoment H pivotMatrix1927 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1927 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1927 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1927 (0 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1927 (0 : Fin 4) = raw3268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1927 raw3268; decide +kernel
    rw [heq]
    exact (canonical3268 hH).trans (sound1277 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1927 (1 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1927 (1 : Fin 4) = raw3042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1927 raw3042; decide +kernel
    rw [heq]
    exact (canonical3042 hH).trans (sound1257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1927 (2 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1927 (2 : Fin 4) = raw3037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1927 raw3037; decide +kernel
    rw [heq]
    exact (canonical3037 hH).trans (sound585 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1927 (3 : Fin 4)) =
      Sparse.eval value1275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1927 (3 : Fin 4) = raw3036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1927 raw3036; decide +kernel
    rw [heq]
    exact (canonical3036 hH).trans (sound1275 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1927 + (injectiveMoment H (mergeFirst pivotMatrix1927 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1927 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1927 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1927 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1927, value1257, value1275, value1277, value585, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1928 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1928 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem sound1928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1928 = Sparse.eval value1928 (momentVector H) := by
  have heq : pivotMatrix1928 = (fun u v => node1928 (pivotPermutation1928 u) v) := by apply Matrix.ext; unfold pivotMatrix1928 node1928 pivotPermutation1928; decide +kernel
  have hmoment : injectiveMoment H node1928 = injectiveMoment H pivotMatrix1928 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1928 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1928 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1928 (0 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1928 (0 : Fin 4) = raw3269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1928 raw3269; decide +kernel
    rw [heq]
    exact (canonical3269 hH).trans (sound477 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1928 (1 : Fin 4)) =
      Sparse.eval value398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1928 (1 : Fin 4) = raw3043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1928 raw3043; decide +kernel
    rw [heq]
    exact (canonical3043 hH).trans (sound398 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1928 (2 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1928 (2 : Fin 4) = raw3038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1928 raw3038; decide +kernel
    rw [heq]
    exact (canonical3038 hH).trans (sound585 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1928 (3 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1928 (3 : Fin 4) = raw3037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1928 raw3037; decide +kernel
    rw [heq]
    exact (canonical3037 hH).trans (sound585 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1928 + (injectiveMoment H (mergeFirst pivotMatrix1928 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1928 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1928 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1928 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1928, value398, value477, value585, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1929 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1929 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem sound1929 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1929 = Sparse.eval value1929 (momentVector H) := by
  have heq : pivotMatrix1929 = (fun u v => node1929 (pivotPermutation1929 u) v) := by apply Matrix.ext; unfold pivotMatrix1929 node1929 pivotPermutation1929; decide +kernel
  have hmoment : injectiveMoment H node1929 = injectiveMoment H pivotMatrix1929 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1929 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1929 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1929 (0 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1929 (0 : Fin 4) = raw3270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1929 raw3270; decide +kernel
    rw [heq]
    exact (canonical3270 hH).trans (sound1235 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1929 (1 : Fin 4)) =
      Sparse.eval value1087 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1929 (1 : Fin 4) = raw3045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1929 raw3045; decide +kernel
    rw [heq]
    exact (canonical3045 hH).trans (sound1087 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1929 (2 : Fin 4)) =
      Sparse.eval value1194 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1929 (2 : Fin 4) = raw3041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1929 raw3041; decide +kernel
    rw [heq]
    exact (canonical3041 hH).trans (sound1194 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1929 (3 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1929 (3 : Fin 4) = raw3040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1929 raw3040; decide +kernel
    rw [heq]
    exact (canonical3040 hH).trans (sound773 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1929 + (injectiveMoment H (mergeFirst pivotMatrix1929 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1929 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1929 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1929 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1929, value1087, value1194, value1235, value773, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1930 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1930 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem sound1930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1930 = Sparse.eval value1930 (momentVector H) := by
  have heq : pivotMatrix1930 = (fun u v => node1930 (pivotPermutation1930 u) v) := by apply Matrix.ext; unfold pivotMatrix1930 node1930 pivotPermutation1930; decide +kernel
  have hmoment : injectiveMoment H node1930 = injectiveMoment H pivotMatrix1930 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1930 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1930 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1930 (0 : Fin 4)) =
      Sparse.eval value776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (0 : Fin 4) = raw4268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw4268; decide +kernel
    rw [heq]
    exact (canonical4268 hH).trans (sound776 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1930 (1 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (1 : Fin 4) = raw3019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw3019; decide +kernel
    rw [heq]
    exact (canonical3019 hH).trans (sound772 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1930 (2 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (2 : Fin 4) = raw2983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw2983; decide +kernel
    rw [heq]
    exact (canonical2983 hH).trans (sound459 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1930 (3 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1930 (3 : Fin 4) = raw2979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1930 raw2979; decide +kernel
    rw [heq]
    exact (canonical2979 hH).trans (sound775 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1930 + (injectiveMoment H (mergeFirst pivotMatrix1930 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1930 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1930 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1930 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1930, value459, value772, value775, value776, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1931 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1931 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem sound1931 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1931 = Sparse.eval value1931 (momentVector H) := by
  have heq : pivotMatrix1931 = (fun u v => node1931 (pivotPermutation1931 u) v) := by apply Matrix.ext; unfold pivotMatrix1931 node1931 pivotPermutation1931; decide +kernel
  have hmoment : injectiveMoment H node1931 = injectiveMoment H pivotMatrix1931 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1931 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1931 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1931 (0 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (0 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1931 (1 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (1 : Fin 4) = raw3021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw3021; decide +kernel
    rw [heq]
    exact (canonical3021 hH).trans (sound397 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1931 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (2 : Fin 4) = raw2985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw2985; decide +kernel
    rw [heq]
    exact (canonical2985 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1931 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1931 (3 : Fin 4) = raw2980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1931 raw2980; decide +kernel
    rw [heq]
    exact (canonical2980 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1931 + (injectiveMoment H (mergeFirst pivotMatrix1931 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1931 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1931 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1931 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1931, value1257, value394, value395, value397, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1932 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1932 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem sound1932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1932 = Sparse.eval value1932 (momentVector H) := by
  have heq : pivotMatrix1932 = (fun u v => node1932 (pivotPermutation1932 u) v) := by apply Matrix.ext; unfold pivotMatrix1932 node1932 pivotPermutation1932; decide +kernel
  have hmoment : injectiveMoment H node1932 = injectiveMoment H pivotMatrix1932 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1932 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1932 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1932 (0 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (0 : Fin 4) = raw6089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw6089; decide +kernel
    rw [heq]
    exact (canonical6089 hH).trans (sound917 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1932 (1 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (1 : Fin 4) = raw3053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw3053; decide +kernel
    rw [heq]
    exact (canonical3053 hH).trans (sound585 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1932 (2 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (2 : Fin 4) = raw2987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw2987; decide +kernel
    rw [heq]
    exact (canonical2987 hH).trans (sound1113 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1932 (3 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (3 : Fin 4) = raw2983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw2983; decide +kernel
    rw [heq]
    exact (canonical2983 hH).trans (sound459 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1932 + (injectiveMoment H (mergeFirst pivotMatrix1932 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1932 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1932 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1932 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1932, value1113, value459, value585, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1933 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1933 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem sound1933 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1933 = Sparse.eval value1933 (momentVector H) := by
  have heq : pivotMatrix1933 = (fun u v => node1933 (pivotPermutation1933 u) v) := by apply Matrix.ext; unfold pivotMatrix1933 node1933 pivotPermutation1933; decide +kernel
  have hmoment : injectiveMoment H node1933 = injectiveMoment H pivotMatrix1933 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1933 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1933 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1933 (0 : Fin 4)) =
      Sparse.eval value920 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (0 : Fin 4) = raw6093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw6093; decide +kernel
    rw [heq]
    exact (canonical6093 hH).trans (sound920 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1933 (1 : Fin 4)) =
      Sparse.eval value1275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (1 : Fin 4) = raw3054 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw3054; decide +kernel
    rw [heq]
    exact (canonical3054 hH).trans (sound1275 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1933 (2 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (2 : Fin 4) = raw2991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw2991; decide +kernel
    rw [heq]
    exact (canonical2991 hH).trans (sound1075 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1933 (3 : Fin 4)) =
      Sparse.eval value582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (3 : Fin 4) = raw2989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw2989; decide +kernel
    rw [heq]
    exact (canonical2989 hH).trans (sound582 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1933 + (injectiveMoment H (mergeFirst pivotMatrix1933 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1933 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1933 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1933 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1933, value1075, value1275, value582, value920, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1934 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1934 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound1934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1934 = Sparse.eval value1934 (momentVector H) := by
  have heq : pivotMatrix1934 = (fun u v => node1934 (pivotPermutation1934 u) v) := by apply Matrix.ext; unfold pivotMatrix1934 node1934 pivotPermutation1934; decide +kernel
  have hmoment : injectiveMoment H node1934 = injectiveMoment H pivotMatrix1934 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1934 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1934 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1934 (0 : Fin 4)) =
      Sparse.eval value918 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1934 (0 : Fin 4) = raw4280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1934 raw4280; decide +kernel
    rw [heq]
    exact (canonical4280 hH).trans (sound918 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1934 (1 : Fin 4)) =
      Sparse.eval value901 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1934 (1 : Fin 4) = raw3035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1934 raw3035; decide +kernel
    rw [heq]
    exact (canonical3035 hH).trans (sound901 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1934 (2 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1934 (2 : Fin 4) = raw3016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1934 raw3016; decide +kernel
    rw [heq]
    exact (canonical3016 hH).trans (sound914 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1934 (3 : Fin 4)) =
      Sparse.eval value900 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1934 (3 : Fin 4) = raw3013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1934 raw3013; decide +kernel
    rw [heq]
    exact (canonical3013 hH).trans (sound900 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1934 + (injectiveMoment H (mergeFirst pivotMatrix1934 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1934 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1934 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1934 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1934, value900, value901, value914, value918, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1935 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1935 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound1935 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1935 = Sparse.eval value1935 (momentVector H) := by
  have heq : pivotMatrix1935 = (fun u v => node1935 (pivotPermutation1935 u) v) := by apply Matrix.ext; unfold pivotMatrix1935 node1935 pivotPermutation1935; decide +kernel
  have hmoment : injectiveMoment H node1935 = injectiveMoment H pivotMatrix1935 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1935 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1935 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1935 (0 : Fin 4)) =
      Sparse.eval value1182 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1935 (0 : Fin 4) = raw4281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1935 raw4281; decide +kernel
    rw [heq]
    exact (canonical4281 hH).trans (sound1182 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1935 (1 : Fin 4)) =
      Sparse.eval value1275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1935 (1 : Fin 4) = raw3036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1935 raw3036; decide +kernel
    rw [heq]
    exact (canonical3036 hH).trans (sound1275 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1935 (2 : Fin 4)) =
      Sparse.eval value1174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1935 (2 : Fin 4) = raw3017 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1935 raw3017; decide +kernel
    rw [heq]
    exact (canonical3017 hH).trans (sound1174 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1935 (3 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1935 (3 : Fin 4) = raw3014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1935 raw3014; decide +kernel
    rw [heq]
    exact (canonical3014 hH).trans (sound1178 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1935 + (injectiveMoment H (mergeFirst pivotMatrix1935 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1935 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1935 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1935 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1935, value1174, value1178, value1182, value1275, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1936 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1936 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem sound1936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1936 = Sparse.eval value1936 (momentVector H) := by
  have heq : pivotMatrix1936 = (fun u v => node1936 (pivotPermutation1936 u) v) := by apply Matrix.ext; unfold pivotMatrix1936 node1936 pivotPermutation1936; decide +kernel
  have hmoment : injectiveMoment H node1936 = injectiveMoment H pivotMatrix1936 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1936 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1936 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1936 (0 : Fin 4)) =
      Sparse.eval value923 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1936 (0 : Fin 4) = raw4282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1936 raw4282; decide +kernel
    rw [heq]
    exact (canonical4282 hH).trans (sound923 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1936 (1 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1936 (1 : Fin 4) = raw3037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1936 raw3037; decide +kernel
    rw [heq]
    exact (canonical3037 hH).trans (sound585 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1936 (2 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1936 (2 : Fin 4) = raw3018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1936 raw3018; decide +kernel
    rw [heq]
    exact (canonical3018 hH).trans (sound914 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1936 (3 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1936 (3 : Fin 4) = raw3015 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1936 raw3015; decide +kernel
    rw [heq]
    exact (canonical3015 hH).trans (sound787 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1936 + (injectiveMoment H (mergeFirst pivotMatrix1936 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1936 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1936 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1936 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1936, value585, value787, value914, value923, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1937 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1937 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound1937 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1937 = Sparse.eval value1937 (momentVector H) := by
  have heq : pivotMatrix1937 = (fun u v => node1937 (pivotPermutation1937 u) v) := by apply Matrix.ext; unfold pivotMatrix1937 node1937 pivotPermutation1937; decide +kernel
  have hmoment : injectiveMoment H node1937 = injectiveMoment H pivotMatrix1937 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1937 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1937 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1937 (0 : Fin 4)) =
      Sparse.eval value1236 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1937 (0 : Fin 4) = raw4284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1937 raw4284; decide +kernel
    rw [heq]
    exact (canonical4284 hH).trans (sound1236 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1937 (1 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1937 (1 : Fin 4) = raw3042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1937 raw3042; decide +kernel
    rw [heq]
    exact (canonical3042 hH).trans (sound1257 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1937 (2 : Fin 4)) =
      Sparse.eval value1243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1937 (2 : Fin 4) = raw3026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1937 raw3026; decide +kernel
    rw [heq]
    exact (canonical3026 hH).trans (sound1243 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1937 (3 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1937 (3 : Fin 4) = raw3024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1937 raw3024; decide +kernel
    rw [heq]
    exact (canonical3024 hH).trans (sound998 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1937 + (injectiveMoment H (mergeFirst pivotMatrix1937 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1937 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1937 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1937 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1937, value1236, value1243, value1257, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1938 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1938 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound1938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1938 = Sparse.eval value1938 (momentVector H) := by
  have heq : pivotMatrix1938 = (fun u v => node1938 (pivotPermutation1938 u) v) := by apply Matrix.ext; unfold pivotMatrix1938 node1938 pivotPermutation1938; decide +kernel
  have hmoment : injectiveMoment H node1938 = injectiveMoment H pivotMatrix1938 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1938 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1938 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1938 (0 : Fin 4)) =
      Sparse.eval value992 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1938 (0 : Fin 4) = raw4286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1938 raw4286; decide +kernel
    rw [heq]
    exact (canonical4286 hH).trans (sound992 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1938 (1 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1938 (1 : Fin 4) = raw3046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1938 raw3046; decide +kernel
    rw [heq]
    exact (canonical3046 hH).trans (sound996 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1938 (2 : Fin 4)) =
      Sparse.eval value1082 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1938 (2 : Fin 4) = raw3030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1938 raw3030; decide +kernel
    rw [heq]
    exact (canonical3030 hH).trans (sound1082 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1938 (3 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1938 (3 : Fin 4) = raw3028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1938 raw3028; decide +kernel
    rw [heq]
    exact (canonical3028 hH).trans (sound1031 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1938 + (injectiveMoment H (mergeFirst pivotMatrix1938 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1938 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1938 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1938 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1938, value1031, value1082, value992, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1939 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1939 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound1939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1939 = Sparse.eval value1939 (momentVector H) := by
  have heq : pivotMatrix1939 = (fun u v => node1939 (pivotPermutation1939 u) v) := by apply Matrix.ext; unfold pivotMatrix1939 node1939 pivotPermutation1939; decide +kernel
  have hmoment : injectiveMoment H node1939 = injectiveMoment H pivotMatrix1939 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1939 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1939 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1939 (0 : Fin 4)) =
      Sparse.eval value1022 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1939 (0 : Fin 4) = raw4288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1939 raw4288; decide +kernel
    rw [heq]
    exact (canonical4288 hH).trans (sound1022 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1939 (1 : Fin 4)) =
      Sparse.eval value1029 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1939 (1 : Fin 4) = raw3047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1939 raw3047; decide +kernel
    rw [heq]
    exact (canonical3047 hH).trans (sound1029 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1939 (2 : Fin 4)) =
      Sparse.eval value1069 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1939 (2 : Fin 4) = raw3032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1939 raw3032; decide +kernel
    rw [heq]
    exact (canonical3032 hH).trans (sound1069 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1939 (3 : Fin 4)) =
      Sparse.eval value1069 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1939 (3 : Fin 4) = raw3031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1939 raw3031; decide +kernel
    rw [heq]
    exact (canonical3031 hH).trans (sound1069 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1939 + (injectiveMoment H (mergeFirst pivotMatrix1939 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1939 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1939 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1939 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1939, value1022, value1029, value1069, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1940 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1940 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound1940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1940 = Sparse.eval value1940 (momentVector H) := by
  have heq : pivotMatrix1940 = (fun u v => node1940 (pivotPermutation1940 u) v) := by apply Matrix.ext; unfold pivotMatrix1940 node1940 pivotPermutation1940; decide +kernel
  have hmoment : injectiveMoment H node1940 = injectiveMoment H pivotMatrix1940 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1940 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1940 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1940 (0 : Fin 4)) =
      Sparse.eval value1251 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (0 : Fin 4) = raw4291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw4291; decide +kernel
    rw [heq]
    exact (canonical4291 hH).trans (sound1251 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1940 (1 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (1 : Fin 4) = raw3064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw3064; decide +kernel
    rw [heq]
    exact (canonical3064 hH).trans (sound1171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1940 (2 : Fin 4)) =
      Sparse.eval value586 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (2 : Fin 4) = raw3057 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw3057; decide +kernel
    rw [heq]
    exact (canonical3057 hH).trans (sound586 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1940 (3 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1940 (3 : Fin 4) = raw3056 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1940 raw3056; decide +kernel
    rw [heq]
    exact (canonical3056 hH).trans (sound1306 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1940 + (injectiveMoment H (mergeFirst pivotMatrix1940 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1940 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1940 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1940 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1940, value1171, value1251, value1306, value586, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1941 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1941 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem sound1941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1941 = Sparse.eval value1941 (momentVector H) := by
  have heq : pivotMatrix1941 = (fun u v => node1941 (pivotPermutation1941 u) v) := by apply Matrix.ext; unfold pivotMatrix1941 node1941 pivotPermutation1941; decide +kernel
  have hmoment : injectiveMoment H node1941 = injectiveMoment H pivotMatrix1941 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1941 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1941 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1941 (0 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (0 : Fin 4) = raw2042 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw2042; decide +kernel
    rw [heq]
    exact (canonical2042 hH).trans (sound1080 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1941 (1 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (1 : Fin 4) = raw3116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw3116; decide +kernel
    rw [heq]
    exact (canonical3116 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1941 (2 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (2 : Fin 4) = raw3213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw3213; decide +kernel
    rw [heq]
    exact (canonical3213 hH).trans (sound1278 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1941 (3 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1941 (3 : Fin 4) = raw3217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1941 raw3217; decide +kernel
    rw [heq]
    exact (canonical3217 hH).trans (sound985 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1941 + (injectiveMoment H (mergeFirst pivotMatrix1941 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1941 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1941 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1941 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1941, value1080, value1278, value246, value985, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1942 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1942 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound1942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1942 = Sparse.eval value1942 (momentVector H) := by
  have heq : pivotMatrix1942 = (fun u v => node1942 (pivotPermutation1942 u) v) := by apply Matrix.ext; unfold pivotMatrix1942 node1942 pivotPermutation1942; decide +kernel
  have hmoment : injectiveMoment H node1942 = injectiveMoment H pivotMatrix1942 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1942 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1942 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1942 (0 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1942 (0 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1942 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1942 (1 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1942 (1 : Fin 4) = raw3134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1942 raw3134; decide +kernel
    rw [heq]
    exact (canonical3134 hH).trans (sound936 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1942 (2 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1942 (2 : Fin 4) = raw3082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1942 raw3082; decide +kernel
    rw [heq]
    exact (canonical3082 hH).trans (sound939 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1942 (3 : Fin 4)) =
      Sparse.eval value505 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1942 (3 : Fin 4) = raw3080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1942 raw3080; decide +kernel
    rw [heq]
    exact (canonical3080 hH).trans (sound505 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1942 + (injectiveMoment H (mergeFirst pivotMatrix1942 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1942 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1942 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1942 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1942, value502, value505, value936, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1943 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1943 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound1943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1943 = Sparse.eval value1943 (momentVector H) := by
  have heq : pivotMatrix1943 = (fun u v => node1943 (pivotPermutation1943 u) v) := by apply Matrix.ext; unfold pivotMatrix1943 node1943 pivotPermutation1943; decide +kernel
  have hmoment : injectiveMoment H node1943 = injectiveMoment H pivotMatrix1943 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1943 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1943 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1943 (0 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1943 (0 : Fin 4) = raw6222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1943 raw6222; decide +kernel
    rw [heq]
    exact (canonical6222 hH).trans (sound944 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1943 (1 : Fin 4)) =
      Sparse.eval value602 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1943 (1 : Fin 4) = raw3276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1943 raw3276; decide +kernel
    rw [heq]
    exact (canonical3276 hH).trans (sound602 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1943 (2 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1943 (2 : Fin 4) = raw3084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1943 raw3084; decide +kernel
    rw [heq]
    exact (canonical3084 hH).trans (sound1007 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1943 (3 : Fin 4)) =
      Sparse.eval value588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1943 (3 : Fin 4) = raw3078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1943 raw3078; decide +kernel
    rw [heq]
    exact (canonical3078 hH).trans (sound588 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1943 + (injectiveMoment H (mergeFirst pivotMatrix1943 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1943 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1943 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1943 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1943, value1007, value588, value602, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1944 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1944 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem sound1944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1944 = Sparse.eval value1944 (momentVector H) := by
  have heq : pivotMatrix1944 = (fun u v => node1944 (pivotPermutation1944 u) v) := by apply Matrix.ext; unfold pivotMatrix1944 node1944 pivotPermutation1944; decide +kernel
  have hmoment : injectiveMoment H node1944 = injectiveMoment H pivotMatrix1944 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1944 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1944 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1944 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1944 (0 : Fin 4) = raw7179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1944 raw7179; decide +kernel
    rw [heq]
    exact (canonical7179 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1944 (1 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1944 (1 : Fin 4) = raw3280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1944 raw3280; decide +kernel
    rw [heq]
    exact (canonical3280 hH).trans (sound603 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1944 (2 : Fin 4)) =
      Sparse.eval value505 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1944 (2 : Fin 4) = raw3085 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1944 raw3085; decide +kernel
    rw [heq]
    exact (canonical3085 hH).trans (sound505 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1944 (3 : Fin 4)) =
      Sparse.eval value588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1944 (3 : Fin 4) = raw3078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1944 raw3078; decide +kernel
    rw [heq]
    exact (canonical3078 hH).trans (sound588 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1944 + (injectiveMoment H (mergeFirst pivotMatrix1944 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1944 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1944 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1944 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1944, value1309, value505, value588, value603, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1945 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1945 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem sound1945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1945 = Sparse.eval value1945 (momentVector H) := by
  have heq : pivotMatrix1945 = (fun u v => node1945 (pivotPermutation1945 u) v) := by apply Matrix.ext; unfold pivotMatrix1945 node1945 pivotPermutation1945; decide +kernel
  have hmoment : injectiveMoment H node1945 = injectiveMoment H pivotMatrix1945 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1945 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1945 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1945 (0 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1945 (0 : Fin 4) = raw6226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1945 raw6226; decide +kernel
    rw [heq]
    exact (canonical6226 hH).trans (sound948 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1945 (1 : Fin 4)) =
      Sparse.eval value597 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1945 (1 : Fin 4) = raw3277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1945 raw3277; decide +kernel
    rw [heq]
    exact (canonical3277 hH).trans (sound597 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1945 (2 : Fin 4)) =
      Sparse.eval value1011 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1945 (2 : Fin 4) = raw3102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1945 raw3102; decide +kernel
    rw [heq]
    exact (canonical3102 hH).trans (sound1011 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1945 (3 : Fin 4)) =
      Sparse.eval value1305 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1945 (3 : Fin 4) = raw3088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1945 raw3088; decide +kernel
    rw [heq]
    exact (canonical3088 hH).trans (sound1305 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1945 + (injectiveMoment H (mergeFirst pivotMatrix1945 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1945 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1945 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1945 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1945, value1011, value1305, value597, value948, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1946 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1946 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound1946 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1946 = Sparse.eval value1946 (momentVector H) := by
  have heq : pivotMatrix1946 = (fun u v => node1946 (pivotPermutation1946 u) v) := by apply Matrix.ext; unfold pivotMatrix1946 node1946 pivotPermutation1946; decide +kernel
  have hmoment : injectiveMoment H node1946 = injectiveMoment H pivotMatrix1946 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1946 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1946 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1946 (0 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1946 (0 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1946 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1946 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1946 (1 : Fin 4) = raw3156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1946 raw3156; decide +kernel
    rw [heq]
    exact (canonical3156 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1946 (2 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1946 (2 : Fin 4) = raw3103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1946 raw3103; decide +kernel
    rw [heq]
    exact (canonical3103 hH).trans (sound950 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1946 (3 : Fin 4)) =
      Sparse.eval value990 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1946 (3 : Fin 4) = raw3101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1946 raw3101; decide +kernel
    rw [heq]
    exact (canonical3101 hH).trans (sound990 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1946 + (injectiveMoment H (mergeFirst pivotMatrix1946 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1946 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1946 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1946 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1946, value1074, value1079, value950, value990, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1947 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1947 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem sound1947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1947 = Sparse.eval value1947 (momentVector H) := by
  have heq : pivotMatrix1947 = (fun u v => node1947 (pivotPermutation1947 u) v) := by apply Matrix.ext; unfold pivotMatrix1947 node1947 pivotPermutation1947; decide +kernel
  have hmoment : injectiveMoment H node1947 = injectiveMoment H pivotMatrix1947 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1947 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1947 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1947 (0 : Fin 4)) =
      Sparse.eval value680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1947 (0 : Fin 4) = raw4484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1947 raw4484; decide +kernel
    rw [heq]
    exact (canonical4484 hH).trans (sound680 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1947 (1 : Fin 4)) =
      Sparse.eval value1105 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1947 (1 : Fin 4) = raw3165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1947 raw3165; decide +kernel
    rw [heq]
    exact (canonical3165 hH).trans (sound1105 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1947 (2 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1947 (2 : Fin 4) = raw3103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1947 raw3103; decide +kernel
    rw [heq]
    exact (canonical3103 hH).trans (sound950 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1947 (3 : Fin 4)) =
      Sparse.eval value519 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1947 (3 : Fin 4) = raw3100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1947 raw3100; decide +kernel
    rw [heq]
    exact (canonical3100 hH).trans (sound519 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1947 + (injectiveMoment H (mergeFirst pivotMatrix1947 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1947 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1947 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1947 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1947, value1105, value519, value680, value950, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1948 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1948 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound1948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1948 = Sparse.eval value1948 (momentVector H) := by
  have heq : pivotMatrix1948 = (fun u v => node1948 (pivotPermutation1948 u) v) := by apply Matrix.ext; unfold pivotMatrix1948 node1948 pivotPermutation1948; decide +kernel
  have hmoment : injectiveMoment H node1948 = injectiveMoment H pivotMatrix1948 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1948 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1948 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1948 (0 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1948 (0 : Fin 4) = raw4485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1948 raw4485; decide +kernel
    rw [heq]
    exact (canonical4485 hH).trans (sound1056 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1948 (1 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1948 (1 : Fin 4) = raw3166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1948 raw3166; decide +kernel
    rw [heq]
    exact (canonical3166 hH).trans (sound1065 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1948 (2 : Fin 4)) =
      Sparse.eval value1001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1948 (2 : Fin 4) = raw3104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1948 raw3104; decide +kernel
    rw [heq]
    exact (canonical3104 hH).trans (sound1001 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1948 (3 : Fin 4)) =
      Sparse.eval value990 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1948 (3 : Fin 4) = raw3101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1948 raw3101; decide +kernel
    rw [heq]
    exact (canonical3101 hH).trans (sound990 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1948 + (injectiveMoment H (mergeFirst pivotMatrix1948 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1948 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1948 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1948 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1948, value1001, value1056, value1065, value990, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1949 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1949 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem sound1949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1949 = Sparse.eval value1949 (momentVector H) := by
  have heq : pivotMatrix1949 = (fun u v => node1949 (pivotPermutation1949 u) v) := by apply Matrix.ext; unfold pivotMatrix1949 node1949 pivotPermutation1949; decide +kernel
  have hmoment : injectiveMoment H node1949 = injectiveMoment H pivotMatrix1949 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1949 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1949 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1949 (0 : Fin 4)) =
      Sparse.eval value951 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1949 (0 : Fin 4) = raw6229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1949 raw6229; decide +kernel
    rw [heq]
    exact (canonical6229 hH).trans (sound951 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1949 (1 : Fin 4)) =
      Sparse.eval value1305 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1949 (1 : Fin 4) = raw3278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1949 raw3278; decide +kernel
    rw [heq]
    exact (canonical3278 hH).trans (sound1305 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1949 (2 : Fin 4)) =
      Sparse.eval value1001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1949 (2 : Fin 4) = raw3105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1949 raw3105; decide +kernel
    rw [heq]
    exact (canonical3105 hH).trans (sound1001 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1949 (3 : Fin 4)) =
      Sparse.eval value589 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1949 (3 : Fin 4) = raw3096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1949 raw3096; decide +kernel
    rw [heq]
    exact (canonical3096 hH).trans (sound589 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1949 + (injectiveMoment H (mergeFirst pivotMatrix1949 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1949 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1949 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1949 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1949, value1001, value1305, value589, value951, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1950 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1950 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem sound1950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1950 = Sparse.eval value1950 (momentVector H) := by
  have heq : pivotMatrix1950 = (fun u v => node1950 (pivotPermutation1950 u) v) := by apply Matrix.ext; unfold pivotMatrix1950 node1950 pivotPermutation1950; decide +kernel
  have hmoment : injectiveMoment H node1950 = injectiveMoment H pivotMatrix1950 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1950 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1950 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1950 (0 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1950 (0 : Fin 4) = raw7185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1950 raw7185; decide +kernel
    rw [heq]
    exact (canonical7185 hH).trans (sound1249 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1950 (1 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1950 (1 : Fin 4) = raw3282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1950 raw3282; decide +kernel
    rw [heq]
    exact (canonical3282 hH).trans (sound604 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1950 (2 : Fin 4)) =
      Sparse.eval value519 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1950 (2 : Fin 4) = raw3107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1950 raw3107; decide +kernel
    rw [heq]
    exact (canonical3107 hH).trans (sound519 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1950 (3 : Fin 4)) =
      Sparse.eval value590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1950 (3 : Fin 4) = raw3099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1950 raw3099; decide +kernel
    rw [heq]
    exact (canonical3099 hH).trans (sound590 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1950 + (injectiveMoment H (mergeFirst pivotMatrix1950 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1950 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1950 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1950 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1950, value1249, value519, value590, value604, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1951 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1951 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound1951 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1951 = Sparse.eval value1951 (momentVector H) := by
  have heq : pivotMatrix1951 = (fun u v => node1951 (pivotPermutation1951 u) v) := by apply Matrix.ext; unfold pivotMatrix1951 node1951 pivotPermutation1951; decide +kernel
  have hmoment : injectiveMoment H node1951 = injectiveMoment H pivotMatrix1951 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1951 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1951 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1951 (0 : Fin 4)) =
      Sparse.eval value952 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1951 (0 : Fin 4) = raw6230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1951 raw6230; decide +kernel
    rw [heq]
    exact (canonical6230 hH).trans (sound952 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1951 (1 : Fin 4)) =
      Sparse.eval value953 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1951 (1 : Fin 4) = raw3279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1951 raw3279; decide +kernel
    rw [heq]
    exact (canonical3279 hH).trans (sound953 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1951 (2 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1951 (2 : Fin 4) = raw3106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1951 raw3106; decide +kernel
    rw [heq]
    exact (canonical3106 hH).trans (sound950 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1951 (3 : Fin 4)) =
      Sparse.eval value590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1951 (3 : Fin 4) = raw3099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1951 raw3099; decide +kernel
    rw [heq]
    exact (canonical3099 hH).trans (sound590 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1951 + (injectiveMoment H (mergeFirst pivotMatrix1951 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1951 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1951 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1951 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1951, value590, value950, value952, value953, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1952 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1952 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem sound1952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1952 = Sparse.eval value1952 (momentVector H) := by
  have heq : pivotMatrix1952 = (fun u v => node1952 (pivotPermutation1952 u) v) := by apply Matrix.ext; unfold pivotMatrix1952 node1952 pivotPermutation1952; decide +kernel
  have hmoment : injectiveMoment H node1952 = injectiveMoment H pivotMatrix1952 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1952 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1952 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1952 (0 : Fin 4)) =
      Sparse.eval value1229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1952 (0 : Fin 4) = raw3003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1952 raw3003; decide +kernel
    rw [heq]
    exact (canonical3003 hH).trans (sound1229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1952 (1 : Fin 4)) =
      Sparse.eval value595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1952 (1 : Fin 4) = raw3178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1952 raw3178; decide +kernel
    rw [heq]
    exact (canonical3178 hH).trans (sound595 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1952 (2 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1952 (2 : Fin 4) = raw3208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1952 raw3208; decide +kernel
    rw [heq]
    exact (canonical3208 hH).trans (sound1269 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1952 (3 : Fin 4)) =
      Sparse.eval value929 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1952 (3 : Fin 4) = raw3212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1952 raw3212; decide +kernel
    rw [heq]
    exact (canonical3212 hH).trans (sound929 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1952 + (injectiveMoment H (mergeFirst pivotMatrix1952 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1952 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1952 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1952 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1952, value1229, value1269, value595, value929, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1953 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1953 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem sound1953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1953 = Sparse.eval value1953 (momentVector H) := by
  have heq : pivotMatrix1953 = (fun u v => node1953 (pivotPermutation1953 u) v) := by apply Matrix.ext; unfold pivotMatrix1953 node1953 pivotPermutation1953; decide +kernel
  have hmoment : injectiveMoment H node1953 = injectiveMoment H pivotMatrix1953 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1953 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1953 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1953 (0 : Fin 4)) =
      Sparse.eval value1338 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1953 (0 : Fin 4) = raw3004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1953 raw3004; decide +kernel
    rw [heq]
    exact (canonical3004 hH).trans (sound1338 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1953 (1 : Fin 4)) =
      Sparse.eval value596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1953 (1 : Fin 4) = raw3179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1953 raw3179; decide +kernel
    rw [heq]
    exact (canonical3179 hH).trans (sound596 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1953 (2 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1953 (2 : Fin 4) = raw3213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1953 raw3213; decide +kernel
    rw [heq]
    exact (canonical3213 hH).trans (sound1278 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1953 (3 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1953 (3 : Fin 4) = raw3214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1953 raw3214; decide +kernel
    rw [heq]
    exact (canonical3214 hH).trans (sound1352 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1953 + (injectiveMoment H (mergeFirst pivotMatrix1953 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1953 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1953 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1953 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1953, value1278, value1338, value1352, value596, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1954 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1954 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound1954 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1954 = Sparse.eval value1954 (momentVector H) := by
  have heq : pivotMatrix1954 = (fun u v => node1954 (pivotPermutation1954 u) v) := by apply Matrix.ext; unfold pivotMatrix1954 node1954 pivotPermutation1954; decide +kernel
  have hmoment : injectiveMoment H node1954 = injectiveMoment H pivotMatrix1954 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1954 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1954 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1954 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1954 (0 : Fin 4) = raw3529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1954 raw3529; decide +kernel
    rw [heq]
    exact (canonical3529 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1954 (1 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1954 (1 : Fin 4) = raw3200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1954 raw3200; decide +kernel
    rw [heq]
    exact (canonical3200 hH).trans (sound1052 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1954 (2 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1954 (2 : Fin 4) = raw3173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1954 raw3173; decide +kernel
    rw [heq]
    exact (canonical3173 hH).trans (sound593 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1954 (3 : Fin 4)) =
      Sparse.eval value1060 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1954 (3 : Fin 4) = raw3171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1954 raw3171; decide +kernel
    rw [heq]
    exact (canonical3171 hH).trans (sound1060 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1954 + (injectiveMoment H (mergeFirst pivotMatrix1954 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1954 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1954 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1954 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1954, value1052, value1059, value1060, value593, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1955 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1955 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

theorem sound1955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1955 = Sparse.eval value1955 (momentVector H) := by
  have heq : pivotMatrix1955 = (fun u v => node1955 (pivotPermutation1955 u) v) := by apply Matrix.ext; unfold pivotMatrix1955 node1955 pivotPermutation1955; decide +kernel
  have hmoment : injectiveMoment H node1955 = injectiveMoment H pivotMatrix1955 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1955 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1955 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1955 (0 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1955 (0 : Fin 4) = raw3531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1955 raw3531; decide +kernel
    rw [heq]
    exact (canonical3531 hH).trans (sound520 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1955 (1 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1955 (1 : Fin 4) = raw3204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1955 raw3204; decide +kernel
    rw [heq]
    exact (canonical3204 hH).trans (sound1056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1955 (2 : Fin 4)) =
      Sparse.eval value594 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1955 (2 : Fin 4) = raw3176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1955 raw3176; decide +kernel
    rw [heq]
    exact (canonical3176 hH).trans (sound594 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1955 (3 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1955 (3 : Fin 4) = raw3173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1955 raw3173; decide +kernel
    rw [heq]
    exact (canonical3173 hH).trans (sound593 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1955 + (injectiveMoment H (mergeFirst pivotMatrix1955 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1955 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1955 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1955 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1955, value1056, value520, value593, value594, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1956 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1956 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem sound1956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1956 = Sparse.eval value1956 (momentVector H) := by
  have heq : pivotMatrix1956 = (fun u v => node1956 (pivotPermutation1956 u) v) := by apply Matrix.ext; unfold pivotMatrix1956 node1956 pivotPermutation1956; decide +kernel
  have hmoment : injectiveMoment H node1956 = injectiveMoment H pivotMatrix1956 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1956 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1956 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1956 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1956 (0 : Fin 4) = raw3567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1956 raw3567; decide +kernel
    rw [heq]
    exact (canonical3567 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1956 (1 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1956 (1 : Fin 4) = raw3227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1956 raw3227; decide +kernel
    rw [heq]
    exact (canonical3227 hH).trans (sound1052 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1956 (2 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1956 (2 : Fin 4) = raw3200 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1956 raw3200; decide +kernel
    rw [heq]
    exact (canonical3200 hH).trans (sound1052 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1956 (3 : Fin 4)) =
      Sparse.eval value956 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1956 (3 : Fin 4) = raw3194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1956 raw3194; decide +kernel
    rw [heq]
    exact (canonical3194 hH).trans (sound956 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1956 + (injectiveMoment H (mergeFirst pivotMatrix1956 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1956 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1956 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1956 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1956, value1027, value1052, value956, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1957 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1957 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound1957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1957 = Sparse.eval value1957 (momentVector H) := by
  have heq : pivotMatrix1957 = (fun u v => node1957 (pivotPermutation1957 u) v) := by apply Matrix.ext; unfold pivotMatrix1957 node1957 pivotPermutation1957; decide +kernel
  have hmoment : injectiveMoment H node1957 = injectiveMoment H pivotMatrix1957 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1957 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1957 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1957 (0 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1957 (0 : Fin 4) = raw3620 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1957 raw3620; decide +kernel
    rw [heq]
    exact (canonical3620 hH).trans (sound1314 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1957 (1 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1957 (1 : Fin 4) = raw3268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1957 raw3268; decide +kernel
    rw [heq]
    exact (canonical3268 hH).trans (sound1277 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1957 (2 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1957 (2 : Fin 4) = raw3262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1957 raw3262; decide +kernel
    rw [heq]
    exact (canonical3262 hH).trans (sound603 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1957 (3 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1957 (3 : Fin 4) = raw3261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1957 raw3261; decide +kernel
    rw [heq]
    exact (canonical3261 hH).trans (sound1313 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1957 + (injectiveMoment H (mergeFirst pivotMatrix1957 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1957 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1957 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1957 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1957, value1277, value1313, value1314, value603, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1958 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1958 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem sound1958 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1958 = Sparse.eval value1958 (momentVector H) := by
  have heq : pivotMatrix1958 = (fun u v => node1958 (pivotPermutation1958 u) v) := by apply Matrix.ext; unfold pivotMatrix1958 node1958 pivotPermutation1958; decide +kernel
  have hmoment : injectiveMoment H node1958 = injectiveMoment H pivotMatrix1958 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1958 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1958 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1958 (0 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1958 (0 : Fin 4) = raw3621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1958 raw3621; decide +kernel
    rw [heq]
    exact (canonical3621 hH).trans (sound608 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1958 (1 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1958 (1 : Fin 4) = raw3269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1958 raw3269; decide +kernel
    rw [heq]
    exact (canonical3269 hH).trans (sound477 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1958 (2 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1958 (2 : Fin 4) = raw3263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1958 raw3263; decide +kernel
    rw [heq]
    exact (canonical3263 hH).trans (sound603 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1958 (3 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1958 (3 : Fin 4) = raw3262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1958 raw3262; decide +kernel
    rw [heq]
    exact (canonical3262 hH).trans (sound603 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1958 + (injectiveMoment H (mergeFirst pivotMatrix1958 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1958 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1958 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1958 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1958, value477, value603, value608, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1959 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1959 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem sound1959 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1959 = Sparse.eval value1959 (momentVector H) := by
  have heq : pivotMatrix1959 = (fun u v => node1959 (pivotPermutation1959 u) v) := by apply Matrix.ext; unfold pivotMatrix1959 node1959 pivotPermutation1959; decide +kernel
  have hmoment : injectiveMoment H node1959 = injectiveMoment H pivotMatrix1959 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1959 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1959 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1959 (0 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1959 (0 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1959 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1959 (1 : Fin 4)) =
      Sparse.eval value594 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1959 (1 : Fin 4) = raw3246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1959 raw3246; decide +kernel
    rw [heq]
    exact (canonical3246 hH).trans (sound594 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1959 (2 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1959 (2 : Fin 4) = raw3150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1959 raw3150; decide +kernel
    rw [heq]
    exact (canonical3150 hH).trans (sound591 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1959 (3 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1959 (3 : Fin 4) = raw3136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1959 raw3136; decide +kernel
    rw [heq]
    exact (canonical3136 hH).trans (sound1315 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1959 + (injectiveMoment H (mergeFirst pivotMatrix1959 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1959 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1959 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1959 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1959, value1315, value591, value594, value683, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1960 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1960 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem sound1960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1960 = Sparse.eval value1960 (momentVector H) := by
  have heq : pivotMatrix1960 = (fun u v => node1960 (pivotPermutation1960 u) v) := by apply Matrix.ext; unfold pivotMatrix1960 node1960 pivotPermutation1960; decide +kernel
  have hmoment : injectiveMoment H node1960 = injectiveMoment H pivotMatrix1960 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1960 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1960 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1960 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (0 : Fin 4) = raw4391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw4391; decide +kernel
    rw [heq]
    exact (canonical4391 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1960 (1 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (1 : Fin 4) = raw3239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw3239; decide +kernel
    rw [heq]
    exact (canonical3239 hH).trans (sound1056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1960 (2 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (2 : Fin 4) = raw3150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw3150; decide +kernel
    rw [heq]
    exact (canonical3150 hH).trans (sound591 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1960 (3 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1960 (3 : Fin 4) = raw3141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1960 raw3141; decide +kernel
    rw [heq]
    exact (canonical3141 hH).trans (sound1301 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1960 + (injectiveMoment H (mergeFirst pivotMatrix1960 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1960 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1960 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1960 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1960, value1056, value1301, value1315, value591, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1961 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1961 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem sound1961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1961 = Sparse.eval value1961 (momentVector H) := by
  have heq : pivotMatrix1961 = (fun u v => node1961 (pivotPermutation1961 u) v) := by apply Matrix.ext; unfold pivotMatrix1961 node1961 pivotPermutation1961; decide +kernel
  have hmoment : injectiveMoment H node1961 = injectiveMoment H pivotMatrix1961 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1961 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1961 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1961 (0 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1961 (0 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1961 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1961 (1 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1961 (1 : Fin 4) = raw3241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1961 raw3241; decide +kernel
    rw [heq]
    exact (canonical3241 hH).trans (sound490 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1961 (2 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1961 (2 : Fin 4) = raw3156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1961 raw3156; decide +kernel
    rw [heq]
    exact (canonical3156 hH).trans (sound1079 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1961 (3 : Fin 4)) =
      Sparse.eval value504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1961 (3 : Fin 4) = raw3154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1961 raw3154; decide +kernel
    rw [heq]
    exact (canonical3154 hH).trans (sound504 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1961 + (injectiveMoment H (mergeFirst pivotMatrix1961 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1961 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1961 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1961 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1961, value1079, value484, value490, value504, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1962 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1962 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]

theorem sound1962 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1962 = Sparse.eval value1962 (momentVector H) := by
  have heq : pivotMatrix1962 = (fun u v => node1962 (pivotPermutation1962 u) v) := by apply Matrix.ext; unfold pivotMatrix1962 node1962 pivotPermutation1962; decide +kernel
  have hmoment : injectiveMoment H node1962 = injectiveMoment H pivotMatrix1962 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1962 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1962 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1962 (0 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1962 (0 : Fin 4) = raw4587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1962 raw4587; decide +kernel
    rw [heq]
    exact (canonical4587 hH).trans (sound520 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1962 (1 : Fin 4)) =
      Sparse.eval value599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1962 (1 : Fin 4) = raw3248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1962 raw3248; decide +kernel
    rw [heq]
    exact (canonical3248 hH).trans (sound599 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1962 (2 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1962 (2 : Fin 4) = raw3157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1962 raw3157; decide +kernel
    rw [heq]
    exact (canonical3157 hH).trans (sound1056 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1962 (3 : Fin 4)) =
      Sparse.eval value504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1962 (3 : Fin 4) = raw3154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1962 raw3154; decide +kernel
    rw [heq]
    exact (canonical3154 hH).trans (sound504 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1962 + (injectiveMoment H (mergeFirst pivotMatrix1962 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1962 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1962 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1962 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1962, value1056, value504, value520, value599, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1963 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1963 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0]]

theorem sound1963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1963 = Sparse.eval value1963 (momentVector H) := by
  have heq : pivotMatrix1963 = (fun u v => node1963 (pivotPermutation1963 u) v) := by apply Matrix.ext; unfold pivotMatrix1963 node1963 pivotPermutation1963; decide +kernel
  have hmoment : injectiveMoment H node1963 = injectiveMoment H pivotMatrix1963 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1963 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1963 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1963 (0 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1963 (0 : Fin 4) = raw7217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1963 raw7217; decide +kernel
    rw [heq]
    exact (canonical7217 hH).trans (sound1314 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1963 (1 : Fin 4)) =
      Sparse.eval value601 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1963 (1 : Fin 4) = raw3287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1963 raw3287; decide +kernel
    rw [heq]
    exact (canonical3287 hH).trans (sound601 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1963 (2 : Fin 4)) =
      Sparse.eval value504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1963 (2 : Fin 4) = raw3159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1963 raw3159; decide +kernel
    rw [heq]
    exact (canonical3159 hH).trans (sound504 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1963 (3 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1963 (3 : Fin 4) = raw3150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1963 raw3150; decide +kernel
    rw [heq]
    exact (canonical3150 hH).trans (sound591 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1963 + (injectiveMoment H (mergeFirst pivotMatrix1963 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1963 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1963 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1963 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1963, value1314, value504, value591, value601, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1964 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1964 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem sound1964 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1964 = Sparse.eval value1964 (momentVector H) := by
  have heq : pivotMatrix1964 = (fun u v => node1964 (pivotPermutation1964 u) v) := by apply Matrix.ext; unfold pivotMatrix1964 node1964 pivotPermutation1964; decide +kernel
  have hmoment : injectiveMoment H node1964 = injectiveMoment H pivotMatrix1964 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1964 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1964 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1964 (0 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1964 (0 : Fin 4) = raw6289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1964 raw6289; decide +kernel
    rw [heq]
    exact (canonical6289 hH).trans (sound975 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1964 (1 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1964 (1 : Fin 4) = raw3280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1964 raw3280; decide +kernel
    rw [heq]
    exact (canonical3280 hH).trans (sound603 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1964 (2 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1964 (2 : Fin 4) = raw3158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1964 raw3158; decide +kernel
    rw [heq]
    exact (canonical3158 hH).trans (sound1056 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1964 (3 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1964 (3 : Fin 4) = raw3150 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1964 raw3150; decide +kernel
    rw [heq]
    exact (canonical3150 hH).trans (sound591 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1964 + (injectiveMoment H (mergeFirst pivotMatrix1964 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1964 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1964 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1964 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1964, value1056, value591, value603, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1965 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1965 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem sound1965 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1965 = Sparse.eval value1965 (momentVector H) := by
  have heq : pivotMatrix1965 = (fun u v => node1965 (pivotPermutation1965 u) v) := by apply Matrix.ext; unfold pivotMatrix1965 node1965 pivotPermutation1965; decide +kernel
  have hmoment : injectiveMoment H node1965 = injectiveMoment H pivotMatrix1965 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1965 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1965 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1965 (0 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1965 (0 : Fin 4) = raw7105 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1965 raw7105; decide +kernel
    rw [heq]
    exact (canonical7105 hH).trans (sound1223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1965 (1 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1965 (1 : Fin 4) = raw3286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1965 raw3286; decide +kernel
    rw [heq]
    exact (canonical3286 hH).trans (sound476 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1965 (2 : Fin 4)) =
      Sparse.eval value504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1965 (2 : Fin 4) = raw3159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1965 raw3159; decide +kernel
    rw [heq]
    exact (canonical3159 hH).trans (sound504 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1965 (3 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1965 (3 : Fin 4) = raw3153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1965 raw3153; decide +kernel
    rw [heq]
    exact (canonical3153 hH).trans (sound474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1965 + (injectiveMoment H (mergeFirst pivotMatrix1965 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1965 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1965 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1965 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1965, value1223, value474, value476, value504, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1966 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1966 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem sound1966 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1966 = Sparse.eval value1966 (momentVector H) := by
  have heq : pivotMatrix1966 = (fun u v => node1966 (pivotPermutation1966 u) v) := by apply Matrix.ext; unfold pivotMatrix1966 node1966 pivotPermutation1966; decide +kernel
  have hmoment : injectiveMoment H node1966 = injectiveMoment H pivotMatrix1966 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1966 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1966 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1966 (0 : Fin 4)) =
      Sparse.eval value1321 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1966 (0 : Fin 4) = raw4406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1966 raw4406; decide +kernel
    rw [heq]
    exact (canonical4406 hH).trans (sound1321 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1966 (1 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1966 (1 : Fin 4) = raw3247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1966 raw3247; decide +kernel
    rw [heq]
    exact (canonical3247 hH).trans (sound1269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1966 (2 : Fin 4)) =
      Sparse.eval value592 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1966 (2 : Fin 4) = raw3164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1966 raw3164; decide +kernel
    rw [heq]
    exact (canonical3164 hH).trans (sound592 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1966 (3 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1966 (3 : Fin 4) = raw3162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1966 raw3162; decide +kernel
    rw [heq]
    exact (canonical3162 hH).trans (sound979 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1966 + (injectiveMoment H (mergeFirst pivotMatrix1966 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1966 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1966 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1966 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1966, value1269, value1321, value592, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1967 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1967 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem sound1967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1967 = Sparse.eval value1967 (momentVector H) := by
  have heq : pivotMatrix1967 = (fun u v => node1967 (pivotPermutation1967 u) v) := by apply Matrix.ext; unfold pivotMatrix1967 node1967 pivotPermutation1967; decide +kernel
  have hmoment : injectiveMoment H node1967 = injectiveMoment H pivotMatrix1967 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1967 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1967 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1967 (0 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1967 (0 : Fin 4) = raw6297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1967 raw6297; decide +kernel
    rw [heq]
    exact (canonical6297 hH).trans (sound979 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1967 (1 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1967 (1 : Fin 4) = raw3281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1967 raw3281; decide +kernel
    rw [heq]
    exact (canonical3281 hH).trans (sound1313 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1967 (2 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1967 (2 : Fin 4) = raw3167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1967 raw3167; decide +kernel
    rw [heq]
    exact (canonical3167 hH).trans (sound1065 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1967 (3 : Fin 4)) =
      Sparse.eval value592 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1967 (3 : Fin 4) = raw3164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1967 raw3164; decide +kernel
    rw [heq]
    exact (canonical3164 hH).trans (sound592 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1967 + (injectiveMoment H (mergeFirst pivotMatrix1967 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1967 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1967 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1967 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1967, value1065, value1313, value592, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1968 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1968 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound1968 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1968 = Sparse.eval value1968 (momentVector H) := by
  have heq : pivotMatrix1968 = (fun u v => node1968 (pivotPermutation1968 u) v) := by apply Matrix.ext; unfold pivotMatrix1968 node1968 pivotPermutation1968; decide +kernel
  have hmoment : injectiveMoment H node1968 = injectiveMoment H pivotMatrix1968 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1968 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1968 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1968 (0 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1968 (0 : Fin 4) = raw4609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1968 raw4609; decide +kernel
    rw [heq]
    exact (canonical4609 hH).trans (sound1310 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1968 (1 : Fin 4)) =
      Sparse.eval value1305 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1968 (1 : Fin 4) = raw3260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1968 raw3260; decide +kernel
    rw [heq]
    exact (canonical3260 hH).trans (sound1305 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1968 (2 : Fin 4)) =
      Sparse.eval value1312 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1968 (2 : Fin 4) = raw3183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1968 raw3183; decide +kernel
    rw [heq]
    exact (canonical3183 hH).trans (sound1312 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1968 (3 : Fin 4)) =
      Sparse.eval value597 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1968 (3 : Fin 4) = raw3180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1968 raw3180; decide +kernel
    rw [heq]
    exact (canonical3180 hH).trans (sound597 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1968 + (injectiveMoment H (mergeFirst pivotMatrix1968 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1968 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1968 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1968 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1968, value1305, value1310, value1312, value597, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1969 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1969 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound1969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1969 = Sparse.eval value1969 (momentVector H) := by
  have heq : pivotMatrix1969 = (fun u v => node1969 (pivotPermutation1969 u) v) := by apply Matrix.ext; unfold pivotMatrix1969 node1969 pivotPermutation1969; decide +kernel
  have hmoment : injectiveMoment H node1969 = injectiveMoment H pivotMatrix1969 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1969 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1969 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1969 (0 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1969 (0 : Fin 4) = raw4610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1969 raw4610; decide +kernel
    rw [heq]
    exact (canonical4610 hH).trans (sound1308 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1969 (1 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1969 (1 : Fin 4) = raw3261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1969 raw3261; decide +kernel
    rw [heq]
    exact (canonical3261 hH).trans (sound1313 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1969 (2 : Fin 4)) =
      Sparse.eval value1312 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1969 (2 : Fin 4) = raw3184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1969 raw3184; decide +kernel
    rw [heq]
    exact (canonical3184 hH).trans (sound1312 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1969 (3 : Fin 4)) =
      Sparse.eval value1307 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1969 (3 : Fin 4) = raw3181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1969 raw3181; decide +kernel
    rw [heq]
    exact (canonical3181 hH).trans (sound1307 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1969 + (injectiveMoment H (mergeFirst pivotMatrix1969 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1969 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1969 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1969 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1969, value1307, value1308, value1312, value1313, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1970 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1970 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem sound1970 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1970 = Sparse.eval value1970 (momentVector H) := by
  have heq : pivotMatrix1970 = (fun u v => node1970 (pivotPermutation1970 u) v) := by apply Matrix.ext; unfold pivotMatrix1970 node1970 pivotPermutation1970; decide +kernel
  have hmoment : injectiveMoment H node1970 = injectiveMoment H pivotMatrix1970 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1970 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1970 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1970 (0 : Fin 4)) =
      Sparse.eval value685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1970 (0 : Fin 4) = raw4611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1970 raw4611; decide +kernel
    rw [heq]
    exact (canonical4611 hH).trans (sound685 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1970 (1 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1970 (1 : Fin 4) = raw3262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1970 raw3262; decide +kernel
    rw [heq]
    exact (canonical3262 hH).trans (sound603 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1970 (2 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1970 (2 : Fin 4) = raw3185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1970 raw3185; decide +kernel
    rw [heq]
    exact (canonical3185 hH).trans (sound1310 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1970 (3 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1970 (3 : Fin 4) = raw3182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1970 raw3182; decide +kernel
    rw [heq]
    exact (canonical3182 hH).trans (sound1308 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1970 + (injectiveMoment H (mergeFirst pivotMatrix1970 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1970 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1970 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1970 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1970, value1308, value1310, value603, value685, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1971 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1971 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem sound1971 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1971 = Sparse.eval value1971 (momentVector H) := by
  have heq : pivotMatrix1971 = (fun u v => node1971 (pivotPermutation1971 u) v) := by apply Matrix.ext; unfold pivotMatrix1971 node1971 pivotPermutation1971; decide +kernel
  have hmoment : injectiveMoment H node1971 = injectiveMoment H pivotMatrix1971 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1971 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1971 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1971 (0 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1971 (0 : Fin 4) = raw6301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1971 raw6301; decide +kernel
    rw [heq]
    exact (canonical6301 hH).trans (sound983 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1971 (1 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1971 (1 : Fin 4) = raw3283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1971 raw3283; decide +kernel
    rw [heq]
    exact (canonical3283 hH).trans (sound1248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1971 (2 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1971 (2 : Fin 4) = raw3185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1971 raw3185; decide +kernel
    rw [heq]
    exact (canonical3185 hH).trans (sound1310 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1971 (3 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1971 (3 : Fin 4) = raw3173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1971 raw3173; decide +kernel
    rw [heq]
    exact (canonical3173 hH).trans (sound593 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1971 + (injectiveMoment H (mergeFirst pivotMatrix1971 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1971 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1971 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1971 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1971, value1248, value1310, value593, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1972 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1972 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem sound1972 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1972 = Sparse.eval value1972 (momentVector H) := by
  have heq : pivotMatrix1972 = (fun u v => node1972 (pivotPermutation1972 u) v) := by apply Matrix.ext; unfold pivotMatrix1972 node1972 pivotPermutation1972; decide +kernel
  have hmoment : injectiveMoment H node1972 = injectiveMoment H pivotMatrix1972 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1972 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1972 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1972 (0 : Fin 4)) =
      Sparse.eval value984 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1972 (0 : Fin 4) = raw6302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1972 raw6302; decide +kernel
    rw [heq]
    exact (canonical6302 hH).trans (sound984 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1972 (1 : Fin 4)) =
      Sparse.eval value1209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1972 (1 : Fin 4) = raw3284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1972 raw3284; decide +kernel
    rw [heq]
    exact (canonical3284 hH).trans (sound1209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1972 (2 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1972 (2 : Fin 4) = raw3186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1972 raw3186; decide +kernel
    rw [heq]
    exact (canonical3186 hH).trans (sound1308 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1972 (3 : Fin 4)) =
      Sparse.eval value594 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1972 (3 : Fin 4) = raw3176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1972 raw3176; decide +kernel
    rw [heq]
    exact (canonical3176 hH).trans (sound594 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1972 + (injectiveMoment H (mergeFirst pivotMatrix1972 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1972 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1972 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1972 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1972, value1209, value1308, value594, value984, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1973 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1973 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound1973 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1973 = Sparse.eval value1973 (momentVector H) := by
  have heq : pivotMatrix1973 = (fun u v => node1973 (pivotPermutation1973 u) v) := by apply Matrix.ext; unfold pivotMatrix1973 node1973 pivotPermutation1973; decide +kernel
  have hmoment : injectiveMoment H node1973 = injectiveMoment H pivotMatrix1973 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1973 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1973 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1973 (0 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1973 (0 : Fin 4) = raw6303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1973 raw6303; decide +kernel
    rw [heq]
    exact (canonical6303 hH).trans (sound985 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1973 (1 : Fin 4)) =
      Sparse.eval value1156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1973 (1 : Fin 4) = raw3285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1973 raw3285; decide +kernel
    rw [heq]
    exact (canonical3285 hH).trans (sound1156 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1973 (2 : Fin 4)) =
      Sparse.eval value1307 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1973 (2 : Fin 4) = raw3187 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1973 raw3187; decide +kernel
    rw [heq]
    exact (canonical3187 hH).trans (sound1307 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1973 (3 : Fin 4)) =
      Sparse.eval value595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1973 (3 : Fin 4) = raw3178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1973 raw3178; decide +kernel
    rw [heq]
    exact (canonical3178 hH).trans (sound595 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1973 + (injectiveMoment H (mergeFirst pivotMatrix1973 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1973 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1973 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1973 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1973, value1156, value1307, value595, value985, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1974 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1974 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem sound1974 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1974 = Sparse.eval value1974 (momentVector H) := by
  have heq : pivotMatrix1974 = (fun u v => node1974 (pivotPermutation1974 u) v) := by apply Matrix.ext; unfold pivotMatrix1974 node1974 pivotPermutation1974; decide +kernel
  have hmoment : injectiveMoment H node1974 = injectiveMoment H pivotMatrix1974 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1974 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1974 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1974 (0 : Fin 4)) =
      Sparse.eval value1230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1974 (0 : Fin 4) = raw4414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1974 raw4414; decide +kernel
    rw [heq]
    exact (canonical4414 hH).trans (sound1230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1974 (1 : Fin 4)) =
      Sparse.eval value595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1974 (1 : Fin 4) = raw3257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1974 raw3257; decide +kernel
    rw [heq]
    exact (canonical3257 hH).trans (sound595 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1974 (2 : Fin 4)) =
      Sparse.eval value985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1974 (2 : Fin 4) = raw3217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1974 raw3217; decide +kernel
    rw [heq]
    exact (canonical3217 hH).trans (sound985 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1974 (3 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1974 (3 : Fin 4) = raw3213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1974 raw3213; decide +kernel
    rw [heq]
    exact (canonical3213 hH).trans (sound1278 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1974 + (injectiveMoment H (mergeFirst pivotMatrix1974 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1974 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1974 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1974 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1974, value1230, value1278, value595, value985, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1975 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1975 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem sound1975 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1975 = Sparse.eval value1975 (momentVector H) := by
  have heq : pivotMatrix1975 = (fun u v => node1975 (pivotPermutation1975 u) v) := by apply Matrix.ext; unfold pivotMatrix1975 node1975 pivotPermutation1975; decide +kernel
  have hmoment : injectiveMoment H node1975 = injectiveMoment H pivotMatrix1975 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1975 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1975 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1975 (0 : Fin 4)) =
      Sparse.eval value1369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1975 (0 : Fin 4) = raw4415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1975 raw4415; decide +kernel
    rw [heq]
    exact (canonical4415 hH).trans (sound1369 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1975 (1 : Fin 4)) =
      Sparse.eval value601 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1975 (1 : Fin 4) = raw3258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1975 raw3258; decide +kernel
    rw [heq]
    exact (canonical3258 hH).trans (sound601 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1975 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1975 (2 : Fin 4) = raw3218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1975 raw3218; decide +kernel
    rw [heq]
    exact (canonical3218 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1975 (3 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1975 (3 : Fin 4) = raw3214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1975 raw3214; decide +kernel
    rw [heq]
    exact (canonical3214 hH).trans (sound1352 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1975 + (injectiveMoment H (mergeFirst pivotMatrix1975 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1975 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1975 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1975 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1975, value1267, value1352, value1369, value601, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1976 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1976 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem sound1976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1976 = Sparse.eval value1976 (momentVector H) := by
  have heq : pivotMatrix1976 = (fun u v => node1976 (pivotPermutation1976 u) v) := by apply Matrix.ext; unfold pivotMatrix1976 node1976 pivotPermutation1976; decide +kernel
  have hmoment : injectiveMoment H node1976 = injectiveMoment H pivotMatrix1976 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1976 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1976 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1976 (0 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1976 (0 : Fin 4) = raw4416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1976 raw4416; decide +kernel
    rw [heq]
    exact (canonical4416 hH).trans (sound1310 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1976 (1 : Fin 4)) =
      Sparse.eval value602 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1976 (1 : Fin 4) = raw3259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1976 raw3259; decide +kernel
    rw [heq]
    exact (canonical3259 hH).trans (sound602 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1976 (2 : Fin 4)) =
      Sparse.eval value1299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1976 (2 : Fin 4) = raw3219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1976 raw3219; decide +kernel
    rw [heq]
    exact (canonical3219 hH).trans (sound1299 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1976 (3 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1976 (3 : Fin 4) = raw3215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1976 raw3215; decide +kernel
    rw [heq]
    exact (canonical3215 hH).trans (sound1007 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1976 + (injectiveMoment H (mergeFirst pivotMatrix1976 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1976 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1976 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1976 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1976, value1007, value1299, value1310, value602, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1977 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1977 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound1977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1977 = Sparse.eval value1977 (momentVector H) := by
  have heq : pivotMatrix1977 = (fun u v => node1977 (pivotPermutation1977 u) v) := by apply Matrix.ext; unfold pivotMatrix1977 node1977 pivotPermutation1977; decide +kernel
  have hmoment : injectiveMoment H node1977 = injectiveMoment H pivotMatrix1977 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1977 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1977 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1977 (0 : Fin 4)) =
      Sparse.eval value1210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1977 (0 : Fin 4) = raw4417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1977 raw4417; decide +kernel
    rw [heq]
    exact (canonical4417 hH).trans (sound1210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1977 (1 : Fin 4)) =
      Sparse.eval value1305 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1977 (1 : Fin 4) = raw3260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1977 raw3260; decide +kernel
    rw [heq]
    exact (canonical3260 hH).trans (sound1305 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1977 (2 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1977 (2 : Fin 4) = raw3220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1977 raw3220; decide +kernel
    rw [heq]
    exact (canonical3220 hH).trans (sound1206 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1977 (3 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1977 (3 : Fin 4) = raw3216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1977 raw3216; decide +kernel
    rw [heq]
    exact (canonical3216 hH).trans (sound948 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1977 + (injectiveMoment H (mergeFirst pivotMatrix1977 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1977 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1977 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1977 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1977, value1206, value1210, value1305, value948, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1978 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1978 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound1978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1978 = Sparse.eval value1978 (momentVector H) := by
  have heq : pivotMatrix1978 = (fun u v => node1978 (pivotPermutation1978 u) v) := by apply Matrix.ext; unfold pivotMatrix1978 node1978 pivotPermutation1978; decide +kernel
  have hmoment : injectiveMoment H node1978 = injectiveMoment H pivotMatrix1978 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1978 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1978 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1978 (0 : Fin 4)) =
      Sparse.eval value1224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1978 (0 : Fin 4) = raw4418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1978 raw4418; decide +kernel
    rw [heq]
    exact (canonical4418 hH).trans (sound1224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1978 (1 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1978 (1 : Fin 4) = raw3261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1978 raw3261; decide +kernel
    rw [heq]
    exact (canonical3261 hH).trans (sound1313 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1978 (2 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1978 (2 : Fin 4) = raw3222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1978 raw3222; decide +kernel
    rw [heq]
    exact (canonical3222 hH).trans (sound977 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1978 (3 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1978 (3 : Fin 4) = raw3218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1978 raw3218; decide +kernel
    rw [heq]
    exact (canonical3218 hH).trans (sound1267 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1978 + (injectiveMoment H (mergeFirst pivotMatrix1978 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1978 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1978 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1978 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1978, value1224, value1267, value1313, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1979 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1979 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem sound1979 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1979 = Sparse.eval value1979 (momentVector H) := by
  have heq : pivotMatrix1979 = (fun u v => node1979 (pivotPermutation1979 u) v) := by apply Matrix.ext; unfold pivotMatrix1979 node1979 pivotPermutation1979; decide +kernel
  have hmoment : injectiveMoment H node1979 = injectiveMoment H pivotMatrix1979 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1979 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1979 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1979 (0 : Fin 4)) =
      Sparse.eval value1361 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1979 (0 : Fin 4) = raw4419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1979 raw4419; decide +kernel
    rw [heq]
    exact (canonical4419 hH).trans (sound1361 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1979 (1 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1979 (1 : Fin 4) = raw3262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1979 raw3262; decide +kernel
    rw [heq]
    exact (canonical3262 hH).trans (sound603 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1979 (2 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1979 (2 : Fin 4) = raw3223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1979 raw3223; decide +kernel
    rw [heq]
    exact (canonical3223 hH).trans (sound1206 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1979 (3 : Fin 4)) =
      Sparse.eval value1299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1979 (3 : Fin 4) = raw3219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1979 raw3219; decide +kernel
    rw [heq]
    exact (canonical3219 hH).trans (sound1299 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1979 + (injectiveMoment H (mergeFirst pivotMatrix1979 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1979 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1979 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1979 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1979, value1206, value1299, value1361, value603, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1980 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1980 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem sound1980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1980 = Sparse.eval value1980 (momentVector H) := by
  have heq : pivotMatrix1980 = (fun u v => node1980 (pivotPermutation1980 u) v) := by apply Matrix.ext; unfold pivotMatrix1980 node1980 pivotPermutation1980; decide +kernel
  have hmoment : injectiveMoment H node1980 = injectiveMoment H pivotMatrix1980 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1980 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1980 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1980 (0 : Fin 4)) =
      Sparse.eval value1213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1980 (0 : Fin 4) = raw4422 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1980 raw4422; decide +kernel
    rw [heq]
    exact (canonical4422 hH).trans (sound1213 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1980 (1 : Fin 4)) =
      Sparse.eval value953 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1980 (1 : Fin 4) = raw3266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1980 raw3266; decide +kernel
    rw [heq]
    exact (canonical3266 hH).trans (sound953 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1980 (2 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1980 (2 : Fin 4) = raw3235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1980 raw3235; decide +kernel
    rw [heq]
    exact (canonical3235 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1980 (3 : Fin 4)) =
      Sparse.eval value1011 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1980 (3 : Fin 4) = raw3233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1980 raw3233; decide +kernel
    rw [heq]
    exact (canonical3233 hH).trans (sound1011 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1980 + (injectiveMoment H (mergeFirst pivotMatrix1980 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1980 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1980 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1980 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1980, value1011, value1207, value1213, value953, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1981 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1981 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem sound1981 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1981 = Sparse.eval value1981 (momentVector H) := by
  have heq : pivotMatrix1981 = (fun u v => node1981 (pivotPermutation1981 u) v) := by apply Matrix.ext; unfold pivotMatrix1981 node1981 pivotPermutation1981; decide +kernel
  have hmoment : injectiveMoment H node1981 = injectiveMoment H pivotMatrix1981 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1981 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1981 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1981 (0 : Fin 4)) =
      Sparse.eval value1327 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1981 (0 : Fin 4) = raw4423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1981 raw4423; decide +kernel
    rw [heq]
    exact (canonical4423 hH).trans (sound1327 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1981 (1 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1981 (1 : Fin 4) = raw3267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1981 raw3267; decide +kernel
    rw [heq]
    exact (canonical3267 hH).trans (sound604 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1981 (2 : Fin 4)) =
      Sparse.eval value1282 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1981 (2 : Fin 4) = raw3237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1981 raw3237; decide +kernel
    rw [heq]
    exact (canonical3237 hH).trans (sound1282 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1981 (3 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1981 (3 : Fin 4) = raw3234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1981 raw3234; decide +kernel
    rw [heq]
    exact (canonical3234 hH).trans (sound1094 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1981 + (injectiveMoment H (mergeFirst pivotMatrix1981 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1981 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1981 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1981 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1981, value1094, value1282, value1327, value604, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1982 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1982 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem sound1982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1982 = Sparse.eval value1982 (momentVector H) := by
  have heq : pivotMatrix1982 = (fun u v => node1982 (pivotPermutation1982 u) v) := by apply Matrix.ext; unfold pivotMatrix1982 node1982 pivotPermutation1982; decide +kernel
  have hmoment : injectiveMoment H node1982 = injectiveMoment H pivotMatrix1982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1982 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1982 (0 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (0 : Fin 4) = raw4427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw4427; decide +kernel
    rw [heq]
    exact (canonical4427 hH).trans (sound1248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1982 (1 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (1 : Fin 4) = raw3270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw3270; decide +kernel
    rw [heq]
    exact (canonical3270 hH).trans (sound1235 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1982 (2 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (2 : Fin 4) = raw3244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw3244; decide +kernel
    rw [heq]
    exact (canonical3244 hH).trans (sound1081 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1982 (3 : Fin 4)) =
      Sparse.eval value598 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1982 (3 : Fin 4) = raw3242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1982 raw3242; decide +kernel
    rw [heq]
    exact (canonical3242 hH).trans (sound598 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1982 + (injectiveMoment H (mergeFirst pivotMatrix1982 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1982 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1982 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1982 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1982, value1081, value1235, value1248, value598, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1983 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1983 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem sound1983 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1983 = Sparse.eval value1983 (momentVector H) := by
  have heq : pivotMatrix1983 = (fun u v => node1983 (pivotPermutation1983 u) v) := by apply Matrix.ext; unfold pivotMatrix1983 node1983 pivotPermutation1983; decide +kernel
  have hmoment : injectiveMoment H node1983 = injectiveMoment H pivotMatrix1983 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1983 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1983 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1983 (0 : Fin 4)) =
      Sparse.eval value676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1983 (0 : Fin 4) = raw4428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1983 raw4428; decide +kernel
    rw [heq]
    exact (canonical4428 hH).trans (sound676 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1983 (1 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1983 (1 : Fin 4) = raw3271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1983 raw3271; decide +kernel
    rw [heq]
    exact (canonical3271 hH).trans (sound483 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1983 (2 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1983 (2 : Fin 4) = raw3245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1983 raw3245; decide +kernel
    rw [heq]
    exact (canonical3245 hH).trans (sound1248 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1983 (3 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1983 (3 : Fin 4) = raw3243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1983 raw3243; decide +kernel
    rw [heq]
    exact (canonical3243 hH).trans (sound995 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1983 + (injectiveMoment H (mergeFirst pivotMatrix1983 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1983 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1983 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1983 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1983, value1248, value483, value676, value995, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
