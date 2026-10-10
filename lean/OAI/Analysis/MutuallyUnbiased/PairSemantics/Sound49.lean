import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical99
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical100
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical103
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical108
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical145

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation3136 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3136 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound3136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3136 = Sparse.eval value3136 (momentVector H) := by
  have heq : pivotMatrix3136 = (fun u v => node3136 (pivotPermutation3136 u) v) := by apply Matrix.ext; unfold pivotMatrix3136 node3136 pivotPermutation3136; decide +kernel
  have hmoment : injectiveMoment H node3136 = injectiveMoment H pivotMatrix3136 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3136 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3136 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3136 (0 : Fin 5)) =
      Sparse.eval value2003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3136 (0 : Fin 5) = raw3492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3136 raw3492; decide +kernel
    rw [heq]
    exact (canonical3492 hH).trans (sound2003 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3136 (1 : Fin 5)) =
      Sparse.eval value1964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3136 (1 : Fin 5) = raw3148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3136 raw3148; decide +kernel
    rw [heq]
    exact (canonical3148 hH).trans (sound1964 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3136 (2 : Fin 5)) =
      Sparse.eval value1652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3136 (2 : Fin 5) = raw3132 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3136 raw3132; decide +kernel
    rw [heq]
    exact (canonical3132 hH).trans (sound1652 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3136 (3 : Fin 5)) =
      Sparse.eval value1958 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3136 (3 : Fin 5) = raw3131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3136 raw3131; decide +kernel
    rw [heq]
    exact (canonical3131 hH).trans (sound1958 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3136 (4 : Fin 5)) =
      Sparse.eval value1957 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3136 (4 : Fin 5) = raw3130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3136 raw3130; decide +kernel
    rw [heq]
    exact (canonical3130 hH).trans (sound1957 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3136 + (injectiveMoment H (mergeFirst pivotMatrix3136 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3136 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3136 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3136 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3136 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3136, value1652, value1957, value1958, value1964, value2003, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3137 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3137 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

theorem sound3137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3137 = Sparse.eval value3137 (momentVector H) := by
  have heq : pivotMatrix3137 = (fun u v => node3137 (pivotPermutation3137 u) v) := by apply Matrix.ext; unfold pivotMatrix3137 node3137 pivotPermutation3137; decide +kernel
  have hmoment : injectiveMoment H node3137 = injectiveMoment H pivotMatrix3137 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3137 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3137 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3137 (0 : Fin 5)) =
      Sparse.eval value2001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3137 (0 : Fin 5) = raw3500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3137 raw3500; decide +kernel
    rw [heq]
    exact (canonical3500 hH).trans (sound2001 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3137 (1 : Fin 5)) =
      Sparse.eval value1966 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3137 (1 : Fin 5) = raw3161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3137 raw3161; decide +kernel
    rw [heq]
    exact (canonical3161 hH).trans (sound1966 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3137 (2 : Fin 5)) =
      Sparse.eval value1633 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3137 (2 : Fin 5) = raw3142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3137 raw3142; decide +kernel
    rw [heq]
    exact (canonical3142 hH).trans (sound1633 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3137 (3 : Fin 5)) =
      Sparse.eval value1633 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3137 (3 : Fin 5) = raw3138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3137 raw3138; decide +kernel
    rw [heq]
    exact (canonical3138 hH).trans (sound1633 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3137 (4 : Fin 5)) =
      Sparse.eval value1960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3137 (4 : Fin 5) = raw3137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3137 raw3137; decide +kernel
    rw [heq]
    exact (canonical3137 hH).trans (sound1960 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3137 + (injectiveMoment H (mergeFirst pivotMatrix3137 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3137 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3137 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3137 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3137 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3137, value1633, value1960, value1966, value2001, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3138 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound3138 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3138 = Sparse.eval value3138 (momentVector H) := by
  have heq : pivotMatrix3138 = (fun u v => node3138 (pivotPermutation3138 u) v) := by apply Matrix.ext; unfold pivotMatrix3138 node3138 pivotPermutation3138; decide +kernel
  have hmoment : injectiveMoment H node3138 = injectiveMoment H pivotMatrix3138 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3138 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3138 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3138 (0 : Fin 5)) =
      Sparse.eval value2001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3138 (0 : Fin 5) = raw3505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3138 raw3505; decide +kernel
    rw [heq]
    exact (canonical3505 hH).trans (sound2001 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3138 (1 : Fin 5)) =
      Sparse.eval value1967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3138 (1 : Fin 5) = raw3163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3138 raw3163; decide +kernel
    rw [heq]
    exact (canonical3163 hH).trans (sound1967 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3138 (2 : Fin 5)) =
      Sparse.eval value1657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3138 (2 : Fin 5) = raw3152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3138 raw3152; decide +kernel
    rw [heq]
    exact (canonical3152 hH).trans (sound1657 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3138 (3 : Fin 5)) =
      Sparse.eval value1964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3138 (3 : Fin 5) = raw3149 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3138 raw3149; decide +kernel
    rw [heq]
    exact (canonical3149 hH).trans (sound1964 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3138 (4 : Fin 5)) =
      Sparse.eval value1964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3138 (4 : Fin 5) = raw3148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3138 raw3148; decide +kernel
    rw [heq]
    exact (canonical3148 hH).trans (sound1964 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3138 + (injectiveMoment H (mergeFirst pivotMatrix3138 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3138 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3138 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3138 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3138 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3138, value1657, value1964, value1967, value2001, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3139 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3139 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound3139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3139 = Sparse.eval value3139 (momentVector H) := by
  have heq : pivotMatrix3139 = (fun u v => node3139 (pivotPermutation3139 u) v) := by apply Matrix.ext; unfold pivotMatrix3139 node3139 pivotPermutation3139; decide +kernel
  have hmoment : injectiveMoment H node3139 = injectiveMoment H pivotMatrix3139 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3139 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3139 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3139 (0 : Fin 5)) =
      Sparse.eval value1743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3139 (0 : Fin 5) = raw3528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3139 raw3528; decide +kernel
    rw [heq]
    exact (canonical3528 hH).trans (sound1743 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3139 (1 : Fin 5)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3139 (1 : Fin 5) = raw3199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3139 raw3199; decide +kernel
    rw [heq]
    exact (canonical3199 hH).trans (sound1634 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3139 (2 : Fin 5)) =
      Sparse.eval value1971 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3139 (2 : Fin 5) = raw3172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3139 raw3172; decide +kernel
    rw [heq]
    exact (canonical3172 hH).trans (sound1971 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3139 (3 : Fin 5)) =
      Sparse.eval value1970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3139 (3 : Fin 5) = raw3170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3139 raw3170; decide +kernel
    rw [heq]
    exact (canonical3170 hH).trans (sound1970 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3139 (4 : Fin 5)) =
      Sparse.eval value1969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3139 (4 : Fin 5) = raw3169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3139 raw3169; decide +kernel
    rw [heq]
    exact (canonical3169 hH).trans (sound1969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3139 + (injectiveMoment H (mergeFirst pivotMatrix3139 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3139 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3139 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3139 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3139 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3139, value1634, value1743, value1969, value1970, value1971, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3140 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound3140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3140 = Sparse.eval value3140 (momentVector H) := by
  have heq : pivotMatrix3140 = (fun u v => node3140 (pivotPermutation3140 u) v) := by apply Matrix.ext; unfold pivotMatrix3140 node3140 pivotPermutation3140; decide +kernel
  have hmoment : injectiveMoment H node3140 = injectiveMoment H pivotMatrix3140 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3140 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3140 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3140 (0 : Fin 5)) =
      Sparse.eval value1695 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3140 (0 : Fin 5) = raw3532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3140 raw3532; decide +kernel
    rw [heq]
    exact (canonical3532 hH).trans (sound1695 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3140 (1 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3140 (1 : Fin 5) = raw3207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3140 raw3207; decide +kernel
    rw [heq]
    exact (canonical3207 hH).trans (sound1644 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3140 (2 : Fin 5)) =
      Sparse.eval value1973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3140 (2 : Fin 5) = raw3177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3140 raw3177; decide +kernel
    rw [heq]
    exact (canonical3177 hH).trans (sound1973 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3140 (3 : Fin 5)) =
      Sparse.eval value1972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3140 (3 : Fin 5) = raw3175 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3140 raw3175; decide +kernel
    rw [heq]
    exact (canonical3175 hH).trans (sound1972 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3140 (4 : Fin 5)) =
      Sparse.eval value1972 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3140 (4 : Fin 5) = raw3174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3140 raw3174; decide +kernel
    rw [heq]
    exact (canonical3174 hH).trans (sound1972 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3140 + (injectiveMoment H (mergeFirst pivotMatrix3140 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3140 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3140 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3140 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3140 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3140, value1644, value1695, value1972, value1973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3141 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3141 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

theorem sound3141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3141 = Sparse.eval value3141 (momentVector H) := by
  have heq : pivotMatrix3141 = (fun u v => node3141 (pivotPermutation3141 u) v) := by apply Matrix.ext; unfold pivotMatrix3141 node3141 pivotPermutation3141; decide +kernel
  have hmoment : injectiveMoment H node3141 = injectiveMoment H pivotMatrix3141 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3141 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3141 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3141 (0 : Fin 5)) =
      Sparse.eval value2013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3141 (0 : Fin 5) = raw3561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3141 raw3561; decide +kernel
    rw [heq]
    exact (canonical3561 hH).trans (sound2013 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3141 (1 : Fin 5)) =
      Sparse.eval value1636 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3141 (1 : Fin 5) = raw3224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3141 raw3224; decide +kernel
    rw [heq]
    exact (canonical3224 hH).trans (sound1636 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3141 (2 : Fin 5)) =
      Sparse.eval value1636 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3141 (2 : Fin 5) = raw3195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3141 raw3195; decide +kernel
    rw [heq]
    exact (canonical3195 hH).trans (sound1636 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3141 (3 : Fin 5)) =
      Sparse.eval value1976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3141 (3 : Fin 5) = raw3190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3141 raw3190; decide +kernel
    rw [heq]
    exact (canonical3190 hH).trans (sound1976 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3141 (4 : Fin 5)) =
      Sparse.eval value1975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3141 (4 : Fin 5) = raw3189 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3141 raw3189; decide +kernel
    rw [heq]
    exact (canonical3189 hH).trans (sound1975 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3141 + (injectiveMoment H (mergeFirst pivotMatrix3141 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3141 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3141 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3141 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3141 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3141, value1636, value1975, value1976, value2013, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3142 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3142 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem sound3142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3142 = Sparse.eval value3142 (momentVector H) := by
  have heq : pivotMatrix3142 = (fun u v => node3142 (pivotPermutation3142 u) v) := by apply Matrix.ext; unfold pivotMatrix3142 node3142 pivotPermutation3142; decide +kernel
  have hmoment : injectiveMoment H node3142 = injectiveMoment H pivotMatrix3142 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3142 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3142 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3142 (0 : Fin 5)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3142 (0 : Fin 5) = raw3562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3142 raw3562; decide +kernel
    rw [heq]
    exact (canonical3562 hH).trans (sound1752 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3142 (1 : Fin 5)) =
      Sparse.eval value1635 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3142 (1 : Fin 5) = raw3225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3142 raw3225; decide +kernel
    rw [heq]
    exact (canonical3225 hH).trans (sound1635 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3142 (2 : Fin 5)) =
      Sparse.eval value1635 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3142 (2 : Fin 5) = raw3196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3142 raw3196; decide +kernel
    rw [heq]
    exact (canonical3196 hH).trans (sound1635 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3142 (3 : Fin 5)) =
      Sparse.eval value1977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3142 (3 : Fin 5) = raw3191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3142 raw3191; decide +kernel
    rw [heq]
    exact (canonical3191 hH).trans (sound1977 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3142 (4 : Fin 5)) =
      Sparse.eval value1976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3142 (4 : Fin 5) = raw3190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3142 raw3190; decide +kernel
    rw [heq]
    exact (canonical3190 hH).trans (sound1976 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3142 + (injectiveMoment H (mergeFirst pivotMatrix3142 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3142 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3142 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3142 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3142 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3142, value1635, value1752, value1976, value1977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3143 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3143 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound3143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3143 = Sparse.eval value3143 (momentVector H) := by
  have heq : pivotMatrix3143 = (fun u v => node3143 (pivotPermutation3143 u) v) := by apply Matrix.ext; unfold pivotMatrix3143 node3143 pivotPermutation3143; decide +kernel
  have hmoment : injectiveMoment H node3143 = injectiveMoment H pivotMatrix3143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3143 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3143 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3143 (0 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3143 (0 : Fin 5) = raw3565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3143 raw3565; decide +kernel
    rw [heq]
    exact (canonical3565 hH).trans (sound1749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3143 (1 : Fin 5)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3143 (1 : Fin 5) = raw3226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3143 raw3226; decide +kernel
    rw [heq]
    exact (canonical3226 hH).trans (sound1634 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3143 (2 : Fin 5)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3143 (2 : Fin 5) = raw3199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3143 raw3199; decide +kernel
    rw [heq]
    exact (canonical3199 hH).trans (sound1634 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3143 (3 : Fin 5)) =
      Sparse.eval value1979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3143 (3 : Fin 5) = raw3193 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3143 raw3193; decide +kernel
    rw [heq]
    exact (canonical3193 hH).trans (sound1979 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3143 (4 : Fin 5)) =
      Sparse.eval value1978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3143 (4 : Fin 5) = raw3192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3143 raw3192; decide +kernel
    rw [heq]
    exact (canonical3192 hH).trans (sound1978 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3143 + (injectiveMoment H (mergeFirst pivotMatrix3143 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3143 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3143 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3143 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3143 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3143, value1634, value1749, value1978, value1979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3144 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3144 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem sound3144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3144 = Sparse.eval value3144 (momentVector H) := by
  have heq : pivotMatrix3144 = (fun u v => node3144 (pivotPermutation3144 u) v) := by apply Matrix.ext; unfold pivotMatrix3144 node3144 pivotPermutation3144; decide +kernel
  have hmoment : injectiveMoment H node3144 = injectiveMoment H pivotMatrix3144 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3144 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3144 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3144 (0 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3144 (0 : Fin 5) = raw3568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3144 raw3568; decide +kernel
    rw [heq]
    exact (canonical3568 hH).trans (sound1800 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3144 (1 : Fin 5)) =
      Sparse.eval value1674 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3144 (1 : Fin 5) = raw3228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3144 raw3228; decide +kernel
    rw [heq]
    exact (canonical3228 hH).trans (sound1674 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3144 (2 : Fin 5)) =
      Sparse.eval value1982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3144 (2 : Fin 5) = raw3202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3144 raw3202; decide +kernel
    rw [heq]
    exact (canonical3202 hH).trans (sound1982 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3144 (3 : Fin 5)) =
      Sparse.eval value1980 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3144 (3 : Fin 5) = raw3197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3144 raw3197; decide +kernel
    rw [heq]
    exact (canonical3197 hH).trans (sound1980 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3144 (4 : Fin 5)) =
      Sparse.eval value1635 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3144 (4 : Fin 5) = raw3196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3144 raw3196; decide +kernel
    rw [heq]
    exact (canonical3196 hH).trans (sound1635 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3144 + (injectiveMoment H (mergeFirst pivotMatrix3144 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3144 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3144 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3144 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3144 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3144, value1635, value1674, value1800, value1980, value1982, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3145 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3145 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem sound3145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3145 = Sparse.eval value3145 (momentVector H) := by
  have heq : pivotMatrix3145 = (fun u v => node3145 (pivotPermutation3145 u) v) := by apply Matrix.ext; unfold pivotMatrix3145 node3145 pivotPermutation3145; decide +kernel
  have hmoment : injectiveMoment H node3145 = injectiveMoment H pivotMatrix3145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3145 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3145 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3145 (0 : Fin 5)) =
      Sparse.eval value1776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3145 (0 : Fin 5) = raw3570 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3145 raw3570; decide +kernel
    rw [heq]
    exact (canonical3570 hH).trans (sound1776 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3145 (1 : Fin 5)) =
      Sparse.eval value1673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3145 (1 : Fin 5) = raw3229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3145 raw3229; decide +kernel
    rw [heq]
    exact (canonical3229 hH).trans (sound1673 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3145 (2 : Fin 5)) =
      Sparse.eval value1983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3145 (2 : Fin 5) = raw3203 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3145 raw3203; decide +kernel
    rw [heq]
    exact (canonical3203 hH).trans (sound1983 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3145 (3 : Fin 5)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3145 (3 : Fin 5) = raw3199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3145 raw3199; decide +kernel
    rw [heq]
    exact (canonical3199 hH).trans (sound1634 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3145 (4 : Fin 5)) =
      Sparse.eval value1981 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3145 (4 : Fin 5) = raw3198 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3145 raw3198; decide +kernel
    rw [heq]
    exact (canonical3198 hH).trans (sound1981 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3145 + (injectiveMoment H (mergeFirst pivotMatrix3145 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3145 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3145 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3145 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3145 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3145, value1634, value1673, value1776, value1981, value1983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3146 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3146 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem sound3146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3146 = Sparse.eval value3146 (momentVector H) := by
  have heq : pivotMatrix3146 = (fun u v => node3146 (pivotPermutation3146 u) v) := by apply Matrix.ext; unfold pivotMatrix3146 node3146 pivotPermutation3146; decide +kernel
  have hmoment : injectiveMoment H node3146 = injectiveMoment H pivotMatrix3146 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3146 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3146 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3146 (0 : Fin 5)) =
      Sparse.eval value2015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3146 (0 : Fin 5) = raw3572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3146 raw3572; decide +kernel
    rw [heq]
    exact (canonical3572 hH).trans (sound2015 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3146 (1 : Fin 5)) =
      Sparse.eval value1686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3146 (1 : Fin 5) = raw3230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3146 raw3230; decide +kernel
    rw [heq]
    exact (canonical3230 hH).trans (sound1686 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3146 (2 : Fin 5)) =
      Sparse.eval value1984 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3146 (2 : Fin 5) = raw3205 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3146 raw3205; decide +kernel
    rw [heq]
    exact (canonical3205 hH).trans (sound1984 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3146 (3 : Fin 5)) =
      Sparse.eval value1982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3146 (3 : Fin 5) = raw3202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3146 raw3202; decide +kernel
    rw [heq]
    exact (canonical3202 hH).trans (sound1982 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3146 (4 : Fin 5)) =
      Sparse.eval value1641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3146 (4 : Fin 5) = raw3201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3146 raw3201; decide +kernel
    rw [heq]
    exact (canonical3201 hH).trans (sound1641 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3146 + (injectiveMoment H (mergeFirst pivotMatrix3146 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3146 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3146 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3146 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3146 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3146, value1641, value1686, value1982, value1984, value2015, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3147 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3147 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound3147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3147 = Sparse.eval value3147 (momentVector H) := by
  have heq : pivotMatrix3147 = (fun u v => node3147 (pivotPermutation3147 u) v) := by apply Matrix.ext; unfold pivotMatrix3147 node3147 pivotPermutation3147; decide +kernel
  have hmoment : injectiveMoment H node3147 = injectiveMoment H pivotMatrix3147 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3147 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3147 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3147 (0 : Fin 5)) =
      Sparse.eval value1698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3147 (0 : Fin 5) = raw3576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3147 raw3576; decide +kernel
    rw [heq]
    exact (canonical3576 hH).trans (sound1698 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3147 (1 : Fin 5)) =
      Sparse.eval value1624 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3147 (1 : Fin 5) = raw3231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3147 raw3231; decide +kernel
    rw [heq]
    exact (canonical3231 hH).trans (sound1624 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3147 (2 : Fin 5)) =
      Sparse.eval value1987 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3147 (2 : Fin 5) = raw3210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3147 raw3210; decide +kernel
    rw [heq]
    exact (canonical3210 hH).trans (sound1987 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3147 (3 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3147 (3 : Fin 5) = raw3207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3147 raw3207; decide +kernel
    rw [heq]
    exact (canonical3207 hH).trans (sound1644 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3147 (4 : Fin 5)) =
      Sparse.eval value1985 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3147 (4 : Fin 5) = raw3206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3147 raw3206; decide +kernel
    rw [heq]
    exact (canonical3206 hH).trans (sound1985 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3147 + (injectiveMoment H (mergeFirst pivotMatrix3147 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3147 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3147 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3147 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3147 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3147, value1624, value1644, value1698, value1985, value1987, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3148 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3148 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

theorem sound3148 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3148 = Sparse.eval value3148 (momentVector H) := by
  have heq : pivotMatrix3148 = (fun u v => node3148 (pivotPermutation3148 u) v) := by apply Matrix.ext; unfold pivotMatrix3148 node3148 pivotPermutation3148; decide +kernel
  have hmoment : injectiveMoment H node3148 = injectiveMoment H pivotMatrix3148 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3148 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3148 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3148 (0 : Fin 5)) =
      Sparse.eval value2196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3148 (0 : Fin 5) = raw4388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3148 raw4388; decide +kernel
    rw [heq]
    exact (canonical4388 hH).trans (sound2196 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3148 (1 : Fin 5)) =
      Sparse.eval value1641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3148 (1 : Fin 5) = raw3238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3148 raw3238; decide +kernel
    rw [heq]
    exact (canonical3238 hH).trans (sound1641 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3148 (2 : Fin 5)) =
      Sparse.eval value1963 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3148 (2 : Fin 5) = raw3147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3148 raw3147; decide +kernel
    rw [heq]
    exact (canonical3147 hH).trans (sound1963 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3148 (3 : Fin 5)) =
      Sparse.eval value2810 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3148 (3 : Fin 5) = raw3140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3148 raw3140; decide +kernel
    rw [heq]
    exact (canonical3140 hH).trans (sound2810 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3148 (4 : Fin 5)) =
      Sparse.eval value1961 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3148 (4 : Fin 5) = raw3139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3148 raw3139; decide +kernel
    rw [heq]
    exact (canonical3139 hH).trans (sound1961 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3148 + (injectiveMoment H (mergeFirst pivotMatrix3148 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3148 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3148 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3148 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3148 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3148, value1641, value1961, value1963, value2196, value2810, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3149 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3149 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem sound3149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3149 = Sparse.eval value3149 (momentVector H) := by
  have heq : pivotMatrix3149 = (fun u v => node3149 (pivotPermutation3149 u) v) := by apply Matrix.ext; unfold pivotMatrix3149 node3149 pivotPermutation3149; decide +kernel
  have hmoment : injectiveMoment H node3149 = injectiveMoment H pivotMatrix3149 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3149 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3149 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3149 (0 : Fin 5)) =
      Sparse.eval value2198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3149 (0 : Fin 5) = raw4392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3149 raw4392; decide +kernel
    rw [heq]
    exact (canonical4392 hH).trans (sound2198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3149 (1 : Fin 5)) =
      Sparse.eval value1686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3149 (1 : Fin 5) = raw3240 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3149 raw3240; decide +kernel
    rw [heq]
    exact (canonical3240 hH).trans (sound1686 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3149 (2 : Fin 5)) =
      Sparse.eval value1965 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3149 (2 : Fin 5) = raw3151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3149 raw3151; decide +kernel
    rw [heq]
    exact (canonical3151 hH).trans (sound1965 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3149 (3 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3149 (3 : Fin 5) = raw3145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3149 raw3145; decide +kernel
    rw [heq]
    exact (canonical3145 hH).trans (sound2740 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3149 (4 : Fin 5)) =
      Sparse.eval value1962 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3149 (4 : Fin 5) = raw3143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3149 raw3143; decide +kernel
    rw [heq]
    exact (canonical3143 hH).trans (sound1962 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3149 + (injectiveMoment H (mergeFirst pivotMatrix3149 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3149 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3149 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3149 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3149 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3149, value1686, value1962, value1965, value2198, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3150 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3150 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem sound3150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3150 = Sparse.eval value3150 (momentVector H) := by
  have heq : pivotMatrix3150 = (fun u v => node3150 (pivotPermutation3150 u) v) := by apply Matrix.ext; unfold pivotMatrix3150 node3150 pivotPermutation3150; decide +kernel
  have hmoment : injectiveMoment H node3150 = injectiveMoment H pivotMatrix3150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3150 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3150 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3150 (0 : Fin 5)) =
      Sparse.eval value2051 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3150 (0 : Fin 5) = raw4438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3150 raw4438; decide +kernel
    rw [heq]
    exact (canonical4438 hH).trans (sound2051 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3150 (1 : Fin 5)) =
      Sparse.eval value2715 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3150 (1 : Fin 5) = raw3354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3150 raw3354; decide +kernel
    rw [heq]
    exact (canonical3354 hH).trans (sound2715 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3150 (2 : Fin 5)) =
      Sparse.eval value1988 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3150 (2 : Fin 5) = raw3297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3150 raw3297; decide +kernel
    rw [heq]
    exact (canonical3297 hH).trans (sound1988 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3150 (3 : Fin 5)) =
      Sparse.eval value1989 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3150 (3 : Fin 5) = raw3295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3150 raw3295; decide +kernel
    rw [heq]
    exact (canonical3295 hH).trans (sound1989 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3150 (4 : Fin 5)) =
      Sparse.eval value1613 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3150 (4 : Fin 5) = raw3294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3150 raw3294; decide +kernel
    rw [heq]
    exact (canonical3294 hH).trans (sound1613 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3150 + (injectiveMoment H (mergeFirst pivotMatrix3150 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3150 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3150 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3150 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3150 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3150, value1613, value1988, value1989, value2051, value2715, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3151 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3151 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound3151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3151 = Sparse.eval value3151 (momentVector H) := by
  have heq : pivotMatrix3151 = (fun u v => node3151 (pivotPermutation3151 u) v) := by apply Matrix.ext; unfold pivotMatrix3151 node3151 pivotPermutation3151; decide +kernel
  have hmoment : injectiveMoment H node3151 = injectiveMoment H pivotMatrix3151 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3151 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3151 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3151 (0 : Fin 5)) =
      Sparse.eval value1940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3151 (0 : Fin 5) = raw3055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3151 raw3055; decide +kernel
    rw [heq]
    exact (canonical3055 hH).trans (sound1940 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3151 (1 : Fin 5)) =
      Sparse.eval value1613 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3151 (1 : Fin 5) = raw3294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3151 raw3294; decide +kernel
    rw [heq]
    exact (canonical3294 hH).trans (sound1613 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3151 (2 : Fin 5)) =
      Sparse.eval value1991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3151 (2 : Fin 5) = raw3302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3151 raw3302; decide +kernel
    rw [heq]
    exact (canonical3302 hH).trans (sound1991 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3151 (3 : Fin 5)) =
      Sparse.eval value1992 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3151 (3 : Fin 5) = raw3304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3151 raw3304; decide +kernel
    rw [heq]
    exact (canonical3304 hH).trans (sound1992 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3151 (4 : Fin 5)) =
      Sparse.eval value1993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3151 (4 : Fin 5) = raw3305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3151 raw3305; decide +kernel
    rw [heq]
    exact (canonical3305 hH).trans (sound1993 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3151 + (injectiveMoment H (mergeFirst pivotMatrix3151 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3151 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3151 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3151 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3151 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3151, value1613, value1940, value1991, value1992, value1993, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3152 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3152 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound3152 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3152 = Sparse.eval value3152 (momentVector H) := by
  have heq : pivotMatrix3152 = (fun u v => node3152 (pivotPermutation3152 u) v) := by apply Matrix.ext; unfold pivotMatrix3152 node3152 pivotPermutation3152; decide +kernel
  have hmoment : injectiveMoment H node3152 = injectiveMoment H pivotMatrix3152 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3152 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3152 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3152 (0 : Fin 5)) =
      Sparse.eval value2057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3152 (0 : Fin 5) = raw3663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3152 raw3663; decide +kernel
    rw [heq]
    exact (canonical3663 hH).trans (sound2057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3152 (1 : Fin 5)) =
      Sparse.eval value2000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3152 (1 : Fin 5) = raw3327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3152 raw3327; decide +kernel
    rw [heq]
    exact (canonical3327 hH).trans (sound2000 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3152 (2 : Fin 5)) =
      Sparse.eval value2828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3152 (2 : Fin 5) = raw3308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3152 raw3308; decide +kernel
    rw [heq]
    exact (canonical3308 hH).trans (sound2828 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3152 (3 : Fin 5)) =
      Sparse.eval value1994 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3152 (3 : Fin 5) = raw3307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3152 raw3307; decide +kernel
    rw [heq]
    exact (canonical3307 hH).trans (sound1994 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3152 (4 : Fin 5)) =
      Sparse.eval value2806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3152 (4 : Fin 5) = raw3306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3152 raw3306; decide +kernel
    rw [heq]
    exact (canonical3306 hH).trans (sound2806 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3152 + (injectiveMoment H (mergeFirst pivotMatrix3152 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3152 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3152 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3152 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3152 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3152, value1994, value2000, value2057, value2806, value2828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3153 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3153 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound3153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3153 = Sparse.eval value3153 (momentVector H) := by
  have heq : pivotMatrix3153 = (fun u v => node3153 (pivotPermutation3153 u) v) := by apply Matrix.ext; unfold pivotMatrix3153 node3153 pivotPermutation3153; decide +kernel
  have hmoment : injectiveMoment H node3153 = injectiveMoment H pivotMatrix3153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3153 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3153 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3153 (0 : Fin 5)) =
      Sparse.eval value2056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3153 (0 : Fin 5) = raw3665 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3153 raw3665; decide +kernel
    rw [heq]
    exact (canonical3665 hH).trans (sound2056 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3153 (1 : Fin 5)) =
      Sparse.eval value1999 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3153 (1 : Fin 5) = raw3333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3153 raw3333; decide +kernel
    rw [heq]
    exact (canonical3333 hH).trans (sound1999 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3153 (2 : Fin 5)) =
      Sparse.eval value1996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3153 (2 : Fin 5) = raw3310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3153 raw3310; decide +kernel
    rw [heq]
    exact (canonical3310 hH).trans (sound1996 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3153 (3 : Fin 5)) =
      Sparse.eval value1995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3153 (3 : Fin 5) = raw3309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3153 raw3309; decide +kernel
    rw [heq]
    exact (canonical3309 hH).trans (sound1995 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3153 (4 : Fin 5)) =
      Sparse.eval value2828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3153 (4 : Fin 5) = raw3308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3153 raw3308; decide +kernel
    rw [heq]
    exact (canonical3308 hH).trans (sound2828 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3153 + (injectiveMoment H (mergeFirst pivotMatrix3153 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3153 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3153 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3153 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3153 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3153, value1995, value1996, value1999, value2056, value2828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3154 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3154 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3154 = Sparse.eval value3154 (momentVector H) := by
  have heq : pivotMatrix3154 = (fun u v => node3154 (pivotPermutation3154 u) v) := by apply Matrix.ext; unfold pivotMatrix3154 node3154 pivotPermutation3154; decide +kernel
  have hmoment : injectiveMoment H node3154 = injectiveMoment H pivotMatrix3154 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3154 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3154 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3154 (0 : Fin 5)) =
      Sparse.eval value2013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3154 (0 : Fin 5) = raw3667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3154 raw3667; decide +kernel
    rw [heq]
    exact (canonical3667 hH).trans (sound2013 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3154 (1 : Fin 5)) =
      Sparse.eval value1998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3154 (1 : Fin 5) = raw3337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3154 raw3337; decide +kernel
    rw [heq]
    exact (canonical3337 hH).trans (sound1998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3154 (2 : Fin 5)) =
      Sparse.eval value2824 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3154 (2 : Fin 5) = raw3315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3154 raw3315; decide +kernel
    rw [heq]
    exact (canonical3315 hH).trans (sound2824 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3154 (3 : Fin 5)) =
      Sparse.eval value1997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3154 (3 : Fin 5) = raw3313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3154 raw3313; decide +kernel
    rw [heq]
    exact (canonical3313 hH).trans (sound1997 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3154 (4 : Fin 5)) =
      Sparse.eval value1997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3154 (4 : Fin 5) = raw3312 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3154 raw3312; decide +kernel
    rw [heq]
    exact (canonical3312 hH).trans (sound1997 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3154 + (injectiveMoment H (mergeFirst pivotMatrix3154 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3154 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3154 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3154 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3154 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3154, value1997, value1998, value2013, value2824, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3155 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3155 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3155 = Sparse.eval value3155 (momentVector H) := by
  have heq : pivotMatrix3155 = (fun u v => node3155 (pivotPermutation3155 u) v) := by apply Matrix.ext; unfold pivotMatrix3155 node3155 pivotPermutation3155; decide +kernel
  have hmoment : injectiveMoment H node3155 = injectiveMoment H pivotMatrix3155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3155 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3155 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3155 (0 : Fin 5)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3155 (0 : Fin 5) = raw4444 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3155 raw4444; decide +kernel
    rw [heq]
    exact (canonical4444 hH).trans (sound1752 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3155 (1 : Fin 5)) =
      Sparse.eval value2851 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3155 (1 : Fin 5) = raw3395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3155 raw3395; decide +kernel
    rw [heq]
    exact (canonical3395 hH).trans (sound2851 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3155 (2 : Fin 5)) =
      Sparse.eval value1998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3155 (2 : Fin 5) = raw3337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3155 raw3337; decide +kernel
    rw [heq]
    exact (canonical3337 hH).trans (sound1998 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3155 (3 : Fin 5)) =
      Sparse.eval value2000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3155 (3 : Fin 5) = raw3328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3155 raw3328; decide +kernel
    rw [heq]
    exact (canonical3328 hH).trans (sound2000 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3155 (4 : Fin 5)) =
      Sparse.eval value2000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3155 (4 : Fin 5) = raw3327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3155 raw3327; decide +kernel
    rw [heq]
    exact (canonical3327 hH).trans (sound2000 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3155 + (injectiveMoment H (mergeFirst pivotMatrix3155 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3155 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3155 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3155 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3155 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3155, value1752, value1998, value2000, value2851, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3156 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3156 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem sound3156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3156 = Sparse.eval value3156 (momentVector H) := by
  have heq : pivotMatrix3156 = (fun u v => node3156 (pivotPermutation3156 u) v) := by apply Matrix.ext; unfold pivotMatrix3156 node3156 pivotPermutation3156; decide +kernel
  have hmoment : injectiveMoment H node3156 = injectiveMoment H pivotMatrix3156 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3156 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3156 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3156 (0 : Fin 5)) =
      Sparse.eval value2015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3156 (0 : Fin 5) = raw4647 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3156 raw4647; decide +kernel
    rw [heq]
    exact (canonical4647 hH).trans (sound2015 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3156 (1 : Fin 5)) =
      Sparse.eval value2752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3156 (1 : Fin 5) = raw3413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3156 raw3413; decide +kernel
    rw [heq]
    exact (canonical3413 hH).trans (sound2752 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3156 (2 : Fin 5)) =
      Sparse.eval value2004 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3156 (2 : Fin 5) = raw3340 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3156 raw3340; decide +kernel
    rw [heq]
    exact (canonical3340 hH).trans (sound2004 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3156 (3 : Fin 5)) =
      Sparse.eval value1999 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3156 (3 : Fin 5) = raw3334 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3156 raw3334; decide +kernel
    rw [heq]
    exact (canonical3334 hH).trans (sound1999 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3156 (4 : Fin 5)) =
      Sparse.eval value2002 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3156 (4 : Fin 5) = raw3331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3156 raw3331; decide +kernel
    rw [heq]
    exact (canonical3331 hH).trans (sound2002 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3156 + (injectiveMoment H (mergeFirst pivotMatrix3156 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3156 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3156 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3156 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3156 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3156, value1999, value2002, value2004, value2015, value2752, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3157 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3157 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound3157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3157 = Sparse.eval value3157 (momentVector H) := by
  have heq : pivotMatrix3157 = (fun u v => node3157 (pivotPermutation3157 u) v) := by apply Matrix.ext; unfold pivotMatrix3157 node3157 pivotPermutation3157; decide +kernel
  have hmoment : injectiveMoment H node3157 = injectiveMoment H pivotMatrix3157 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3157 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3157 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3157 (0 : Fin 5)) =
      Sparse.eval value2609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3157 (0 : Fin 5) = raw4648 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3157 raw4648; decide +kernel
    rw [heq]
    exact (canonical4648 hH).trans (sound2609 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3157 (1 : Fin 5)) =
      Sparse.eval value2609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3157 (1 : Fin 5) = raw3414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3157 raw3414; decide +kernel
    rw [heq]
    exact (canonical3414 hH).trans (sound2609 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3157 (2 : Fin 5)) =
      Sparse.eval value2001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3157 (2 : Fin 5) = raw3341 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3157 raw3341; decide +kernel
    rw [heq]
    exact (canonical3341 hH).trans (sound2001 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3157 (3 : Fin 5)) =
      Sparse.eval value2003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3157 (3 : Fin 5) = raw3335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3157 raw3335; decide +kernel
    rw [heq]
    exact (canonical3335 hH).trans (sound2003 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3157 (4 : Fin 5)) =
      Sparse.eval value2003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3157 (4 : Fin 5) = raw3332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3157 raw3332; decide +kernel
    rw [heq]
    exact (canonical3332 hH).trans (sound2003 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3157 + (injectiveMoment H (mergeFirst pivotMatrix3157 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3157 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3157 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3157 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3157 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3157, value2001, value2003, value2609, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3158 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3158 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound3158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3158 = Sparse.eval value3158 (momentVector H) := by
  have heq : pivotMatrix3158 = (fun u v => node3158 (pivotPermutation3158 u) v) := by apply Matrix.ext; unfold pivotMatrix3158 node3158 pivotPermutation3158; decide +kernel
  have hmoment : injectiveMoment H node3158 = injectiveMoment H pivotMatrix3158 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3158 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3158 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3158 (0 : Fin 5)) =
      Sparse.eval value1727 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3158 (0 : Fin 5) = raw2156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3158 raw2156; decide +kernel
    rw [heq]
    exact (canonical2156 hH).trans (sound1727 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3158 (1 : Fin 5)) =
      Sparse.eval value1613 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3158 (1 : Fin 5) = raw3294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3158 raw3294; decide +kernel
    rw [heq]
    exact (canonical3294 hH).trans (sound1613 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3158 (2 : Fin 5)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3158 (2 : Fin 5) = raw3352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3158 raw3352; decide +kernel
    rw [heq]
    exact (canonical3352 hH).trans (sound771 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3158 (3 : Fin 5)) =
      Sparse.eval value1562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3158 (3 : Fin 5) = raw3353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3158 raw3353; decide +kernel
    rw [heq]
    exact (canonical3353 hH).trans (sound1562 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3158 (4 : Fin 5)) =
      Sparse.eval value2715 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3158 (4 : Fin 5) = raw3354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3158 raw3354; decide +kernel
    rw [heq]
    exact (canonical3354 hH).trans (sound2715 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3158 + (injectiveMoment H (mergeFirst pivotMatrix3158 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3158 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3158 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3158 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3158 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3158, value1562, value1613, value1727, value2715, value771, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3159 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3159 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound3159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3159 = Sparse.eval value3159 (momentVector H) := by
  have heq : pivotMatrix3159 = (fun u v => node3159 (pivotPermutation3159 u) v) := by apply Matrix.ext; unfold pivotMatrix3159 node3159 pivotPermutation3159; decide +kernel
  have hmoment : injectiveMoment H node3159 = injectiveMoment H pivotMatrix3159 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3159 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3159 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3159 (0 : Fin 5)) =
      Sparse.eval value2202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3159 (0 : Fin 5) = raw4448 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3159 raw4448; decide +kernel
    rw [heq]
    exact (canonical4448 hH).trans (sound2202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3159 (1 : Fin 5)) =
      Sparse.eval value2808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3159 (1 : Fin 5) = raw3429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3159 raw3429; decide +kernel
    rw [heq]
    exact (canonical3429 hH).trans (sound2808 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3159 (2 : Fin 5)) =
      Sparse.eval value2006 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3159 (2 : Fin 5) = raw3360 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3159 raw3360; decide +kernel
    rw [heq]
    exact (canonical3360 hH).trans (sound2006 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3159 (3 : Fin 5)) =
      Sparse.eval value2715 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3159 (3 : Fin 5) = raw3354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3159 raw3354; decide +kernel
    rw [heq]
    exact (canonical3354 hH).trans (sound2715 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3159 (4 : Fin 5)) =
      Sparse.eval value1562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3159 (4 : Fin 5) = raw3353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3159 raw3353; decide +kernel
    rw [heq]
    exact (canonical3353 hH).trans (sound1562 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3159 + (injectiveMoment H (mergeFirst pivotMatrix3159 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3159 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3159 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3159 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3159 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3159, value1562, value2006, value2202, value2715, value2808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3160 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3160 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3160 = Sparse.eval value3160 (momentVector H) := by
  have heq : pivotMatrix3160 = (fun u v => node3160 (pivotPermutation3160 u) v) := by apply Matrix.ext; unfold pivotMatrix3160 node3160 pivotPermutation3160; decide +kernel
  have hmoment : injectiveMoment H node3160 = injectiveMoment H pivotMatrix3160 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3160 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3160 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3160 (0 : Fin 5)) =
      Sparse.eval value2203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (0 : Fin 5) = raw4449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw4449; decide +kernel
    rw [heq]
    exact (canonical4449 hH).trans (sound2203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3160 (1 : Fin 5)) =
      Sparse.eval value2687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (1 : Fin 5) = raw3437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3437; decide +kernel
    rw [heq]
    exact (canonical3437 hH).trans (sound2687 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3160 (2 : Fin 5)) =
      Sparse.eval value1477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (2 : Fin 5) = raw3362 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3362; decide +kernel
    rw [heq]
    exact (canonical3362 hH).trans (sound1477 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3160 (3 : Fin 5)) =
      Sparse.eval value2683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (3 : Fin 5) = raw3358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3358; decide +kernel
    rw [heq]
    exact (canonical3358 hH).trans (sound2683 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3160 (4 : Fin 5)) =
      Sparse.eval value2005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (4 : Fin 5) = raw3357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3357; decide +kernel
    rw [heq]
    exact (canonical3357 hH).trans (sound2005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3160 + (injectiveMoment H (mergeFirst pivotMatrix3160 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3160, value1477, value2005, value2203, value2683, value2687, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3161 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3161 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound3161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3161 = Sparse.eval value3161 (momentVector H) := by
  have heq : pivotMatrix3161 = (fun u v => node3161 (pivotPermutation3161 u) v) := by apply Matrix.ext; unfold pivotMatrix3161 node3161 pivotPermutation3161; decide +kernel
  have hmoment : injectiveMoment H node3161 = injectiveMoment H pivotMatrix3161 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3161 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3161 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3161 (0 : Fin 5)) =
      Sparse.eval value1637 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3161 (0 : Fin 5) = raw1763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3161 raw1763; decide +kernel
    rw [heq]
    exact (canonical1763 hH).trans (sound1637 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3161 (1 : Fin 5)) =
      Sparse.eval value1993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3161 (1 : Fin 5) = raw3305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3161 raw3305; decide +kernel
    rw [heq]
    exact (canonical3305 hH).trans (sound1993 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3161 (2 : Fin 5)) =
      Sparse.eval value2533 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3161 (2 : Fin 5) = raw3381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3161 raw3381; decide +kernel
    rw [heq]
    exact (canonical3381 hH).trans (sound2533 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3161 (3 : Fin 5)) =
      Sparse.eval value2016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3161 (3 : Fin 5) = raw3392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3161 raw3392; decide +kernel
    rw [heq]
    exact (canonical3392 hH).trans (sound2016 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3161 (4 : Fin 5)) =
      Sparse.eval value2743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3161 (4 : Fin 5) = raw3394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3161 raw3394; decide +kernel
    rw [heq]
    exact (canonical3394 hH).trans (sound2743 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3161 + (injectiveMoment H (mergeFirst pivotMatrix3161 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3161 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3161 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3161 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3161 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3161, value1637, value1993, value2016, value2533, value2743, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3162 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3162 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem sound3162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3162 = Sparse.eval value3162 (momentVector H) := by
  have heq : pivotMatrix3162 = (fun u v => node3162 (pivotPermutation3162 u) v) := by apply Matrix.ext; unfold pivotMatrix3162 node3162 pivotPermutation3162; decide +kernel
  have hmoment : injectiveMoment H node3162 = injectiveMoment H pivotMatrix3162 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3162 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3162 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3162 (0 : Fin 5)) =
      Sparse.eval value1714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3162 (0 : Fin 5) = raw2016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3162 raw2016; decide +kernel
    rw [heq]
    exact (canonical2016 hH).trans (sound1714 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3162 (1 : Fin 5)) =
      Sparse.eval value2807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3162 (1 : Fin 5) = raw3469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3162 raw3469; decide +kernel
    rw [heq]
    exact (canonical3469 hH).trans (sound2807 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3162 (2 : Fin 5)) =
      Sparse.eval value2807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3162 (2 : Fin 5) = raw3551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3162 raw3551; decide +kernel
    rw [heq]
    exact (canonical3551 hH).trans (sound2807 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3162 (3 : Fin 5)) =
      Sparse.eval value2047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3162 (3 : Fin 5) = raw3559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3162 raw3559; decide +kernel
    rw [heq]
    exact (canonical3559 hH).trans (sound2047 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3162 (4 : Fin 5)) =
      Sparse.eval value2048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3162 (4 : Fin 5) = raw3564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3162 raw3564; decide +kernel
    rw [heq]
    exact (canonical3564 hH).trans (sound2048 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3162 + (injectiveMoment H (mergeFirst pivotMatrix3162 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3162 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3162 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3162 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3162 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3162, value1714, value2047, value2048, value2807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3163 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3163 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem sound3163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3163 = Sparse.eval value3163 (momentVector H) := by
  have heq : pivotMatrix3163 = (fun u v => node3163 (pivotPermutation3163 u) v) := by apply Matrix.ext; unfold pivotMatrix3163 node3163 pivotPermutation3163; decide +kernel
  have hmoment : injectiveMoment H node3163 = injectiveMoment H pivotMatrix3163 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3163 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3163 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3163 (0 : Fin 5)) =
      Sparse.eval value1717 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3163 (0 : Fin 5) = raw2020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3163 raw2020; decide +kernel
    rw [heq]
    exact (canonical2020 hH).trans (sound1717 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3163 (1 : Fin 5)) =
      Sparse.eval value2754 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3163 (1 : Fin 5) = raw3471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3163 raw3471; decide +kernel
    rw [heq]
    exact (canonical3471 hH).trans (sound2754 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3163 (2 : Fin 5)) =
      Sparse.eval value2754 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3163 (2 : Fin 5) = raw3552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3163 raw3552; decide +kernel
    rw [heq]
    exact (canonical3552 hH).trans (sound2754 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3163 (3 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3163 (3 : Fin 5) = raw3563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3163 raw3563; decide +kernel
    rw [heq]
    exact (canonical3563 hH).trans (sound1507 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3163 (4 : Fin 5)) =
      Sparse.eval value2048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3163 (4 : Fin 5) = raw3566 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3163 raw3566; decide +kernel
    rw [heq]
    exact (canonical3566 hH).trans (sound2048 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3163 + (injectiveMoment H (mergeFirst pivotMatrix3163 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3163 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3163 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3163 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3163 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3163, value1507, value1717, value2048, value2754, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3164 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3164 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound3164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3164 = Sparse.eval value3164 (momentVector H) := by
  have heq : pivotMatrix3164 = (fun u v => node3164 (pivotPermutation3164 u) v) := by apply Matrix.ext; unfold pivotMatrix3164 node3164 pivotPermutation3164; decide +kernel
  have hmoment : injectiveMoment H node3164 = injectiveMoment H pivotMatrix3164 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3164 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3164 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3164 (0 : Fin 5)) =
      Sparse.eval value1722 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3164 (0 : Fin 5) = raw2039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3164 raw2039; decide +kernel
    rw [heq]
    exact (canonical2039 hH).trans (sound1722 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3164 (1 : Fin 5)) =
      Sparse.eval value2686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3164 (1 : Fin 5) = raw3473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3164 raw3473; decide +kernel
    rw [heq]
    exact (canonical3473 hH).trans (sound2686 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3164 (2 : Fin 5)) =
      Sparse.eval value2764 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3164 (2 : Fin 5) = raw3553 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3164 raw3553; decide +kernel
    rw [heq]
    exact (canonical3553 hH).trans (sound2764 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3164 (3 : Fin 5)) =
      Sparse.eval value2051 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3164 (3 : Fin 5) = raw3578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3164 raw3578; decide +kernel
    rw [heq]
    exact (canonical3578 hH).trans (sound2051 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3164 (4 : Fin 5)) =
      Sparse.eval value2054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3164 (4 : Fin 5) = raw3581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3164 raw3581; decide +kernel
    rw [heq]
    exact (canonical3581 hH).trans (sound2054 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3164 + (injectiveMoment H (mergeFirst pivotMatrix3164 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3164 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3164 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3164 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3164 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3164, value1722, value2051, value2054, value2686, value2764, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3165 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3165 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound3165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3165 = Sparse.eval value3165 (momentVector H) := by
  have heq : pivotMatrix3165 = (fun u v => node3165 (pivotPermutation3165 u) v) := by apply Matrix.ext; unfold pivotMatrix3165 node3165 pivotPermutation3165; decide +kernel
  have hmoment : injectiveMoment H node3165 = injectiveMoment H pivotMatrix3165 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3165 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3165 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3165 (0 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (0 : Fin 5) = raw2191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw2191; decide +kernel
    rw [heq]
    exact (canonical2191 hH).trans (sound1746 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3165 (1 : Fin 5)) =
      Sparse.eval value1998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (1 : Fin 5) = raw3325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3325; decide +kernel
    rw [heq]
    exact (canonical3325 hH).trans (sound1998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3165 (2 : Fin 5)) =
      Sparse.eval value1357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (2 : Fin 5) = raw3382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3382; decide +kernel
    rw [heq]
    exact (canonical3382 hH).trans (sound1357 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3165 (3 : Fin 5)) =
      Sparse.eval value1357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (3 : Fin 5) = raw3388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3388; decide +kernel
    rw [heq]
    exact (canonical3388 hH).trans (sound1357 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3165 (4 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (4 : Fin 5) = raw3390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3390; decide +kernel
    rw [heq]
    exact (canonical3390 hH).trans (sound1746 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3165 + (injectiveMoment H (mergeFirst pivotMatrix3165 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3165, value1357, value1746, value1998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3166 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3166 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound3166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3166 = Sparse.eval value3166 (momentVector H) := by
  have heq : pivotMatrix3166 = (fun u v => node3166 (pivotPermutation3166 u) v) := by apply Matrix.ext; unfold pivotMatrix3166 node3166 pivotPermutation3166; decide +kernel
  have hmoment : injectiveMoment H node3166 = injectiveMoment H pivotMatrix3166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3166 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3166 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3166 (0 : Fin 5)) =
      Sparse.eval value1747 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3166 (0 : Fin 5) = raw2192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3166 raw2192; decide +kernel
    rw [heq]
    exact (canonical2192 hH).trans (sound1747 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3166 (1 : Fin 5)) =
      Sparse.eval value1999 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3166 (1 : Fin 5) = raw3326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3166 raw3326; decide +kernel
    rw [heq]
    exact (canonical3326 hH).trans (sound1999 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3166 (2 : Fin 5)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3166 (2 : Fin 5) = raw3383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3166 raw3383; decide +kernel
    rw [heq]
    exact (canonical3383 hH).trans (sound1264 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3166 (3 : Fin 5)) =
      Sparse.eval value2743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3166 (3 : Fin 5) = raw3389 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3166 raw3389; decide +kernel
    rw [heq]
    exact (canonical3389 hH).trans (sound2743 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3166 (4 : Fin 5)) =
      Sparse.eval value2743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3166 (4 : Fin 5) = raw3391 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3166 raw3391; decide +kernel
    rw [heq]
    exact (canonical3391 hH).trans (sound2743 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3166 + (injectiveMoment H (mergeFirst pivotMatrix3166 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3166 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3166 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3166 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3166 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3166, value1264, value1747, value1999, value2743, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3167 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3167 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound3167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3167 = Sparse.eval value3167 (momentVector H) := by
  have heq : pivotMatrix3167 = (fun u v => node3167 (pivotPermutation3167 u) v) := by apply Matrix.ext; unfold pivotMatrix3167 node3167 pivotPermutation3167; decide +kernel
  have hmoment : injectiveMoment H node3167 = injectiveMoment H pivotMatrix3167 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3167 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3167 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3167 (0 : Fin 5)) =
      Sparse.eval value1748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3167 (0 : Fin 5) = raw2194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3167 raw2194; decide +kernel
    rw [heq]
    exact (canonical2194 hH).trans (sound1748 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3167 (1 : Fin 5)) =
      Sparse.eval value2000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3167 (1 : Fin 5) = raw3327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3167 raw3327; decide +kernel
    rw [heq]
    exact (canonical3327 hH).trans (sound2000 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3167 (2 : Fin 5)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3167 (2 : Fin 5) = raw3384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3167 raw3384; decide +kernel
    rw [heq]
    exact (canonical3384 hH).trans (sound1241 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3167 (3 : Fin 5)) =
      Sparse.eval value2017 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3167 (3 : Fin 5) = raw3393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3167 raw3393; decide +kernel
    rw [heq]
    exact (canonical3393 hH).trans (sound2017 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3167 (4 : Fin 5)) =
      Sparse.eval value2851 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3167 (4 : Fin 5) = raw3395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3167 raw3395; decide +kernel
    rw [heq]
    exact (canonical3395 hH).trans (sound2851 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3167 + (injectiveMoment H (mergeFirst pivotMatrix3167 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3167 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3167 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3167 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3167 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3167, value1241, value1748, value2000, value2017, value2851, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3168 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3168 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound3168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3168 = Sparse.eval value3168 (momentVector H) := by
  have heq : pivotMatrix3168 = (fun u v => node3168 (pivotPermutation3168 u) v) := by apply Matrix.ext; unfold pivotMatrix3168 node3168 pivotPermutation3168; decide +kernel
  have hmoment : injectiveMoment H node3168 = injectiveMoment H pivotMatrix3168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3168 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3168 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3168 (0 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3168 (0 : Fin 5) = raw2195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3168 raw2195; decide +kernel
    rw [heq]
    exact (canonical2195 hH).trans (sound1749 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3168 (1 : Fin 5)) =
      Sparse.eval value2001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3168 (1 : Fin 5) = raw3330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3168 raw3330; decide +kernel
    rw [heq]
    exact (canonical3330 hH).trans (sound2001 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3168 (2 : Fin 5)) =
      Sparse.eval value2745 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3168 (2 : Fin 5) = raw3385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3168 raw3385; decide +kernel
    rw [heq]
    exact (canonical3385 hH).trans (sound2745 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3168 (3 : Fin 5)) =
      Sparse.eval value2745 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3168 (3 : Fin 5) = raw3397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3168 raw3397; decide +kernel
    rw [heq]
    exact (canonical3397 hH).trans (sound2745 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3168 (4 : Fin 5)) =
      Sparse.eval value2613 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3168 (4 : Fin 5) = raw3398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3168 raw3398; decide +kernel
    rw [heq]
    exact (canonical3398 hH).trans (sound2613 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3168 + (injectiveMoment H (mergeFirst pivotMatrix3168 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3168 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3168 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3168 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3168 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3168, value1749, value2001, value2613, value2745, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3169 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3169 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound3169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3169 = Sparse.eval value3169 (momentVector H) := by
  have heq : pivotMatrix3169 = (fun u v => node3169 (pivotPermutation3169 u) v) := by apply Matrix.ext; unfold pivotMatrix3169 node3169 pivotPermutation3169; decide +kernel
  have hmoment : injectiveMoment H node3169 = injectiveMoment H pivotMatrix3169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3169 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3169 (0 : Fin 5)) =
      Sparse.eval value1750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3169 (0 : Fin 5) = raw2196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3169 raw2196; decide +kernel
    rw [heq]
    exact (canonical2196 hH).trans (sound1750 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3169 (1 : Fin 5)) =
      Sparse.eval value2003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3169 (1 : Fin 5) = raw3332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3169 raw3332; decide +kernel
    rw [heq]
    exact (canonical3332 hH).trans (sound2003 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3169 (2 : Fin 5)) =
      Sparse.eval value2629 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3169 (2 : Fin 5) = raw3386 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3169 raw3386; decide +kernel
    rw [heq]
    exact (canonical3386 hH).trans (sound2629 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3169 (3 : Fin 5)) =
      Sparse.eval value2629 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3169 (3 : Fin 5) = raw3399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3169 raw3399; decide +kernel
    rw [heq]
    exact (canonical3399 hH).trans (sound2629 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3169 (4 : Fin 5)) =
      Sparse.eval value2784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3169 (4 : Fin 5) = raw3401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3169 raw3401; decide +kernel
    rw [heq]
    exact (canonical3401 hH).trans (sound2784 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3169 + (injectiveMoment H (mergeFirst pivotMatrix3169 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3169 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3169 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3169 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3169 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3169, value1750, value2003, value2629, value2784, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3170 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3170 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound3170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3170 = Sparse.eval value3170 (momentVector H) := by
  have heq : pivotMatrix3170 = (fun u v => node3170 (pivotPermutation3170 u) v) := by apply Matrix.ext; unfold pivotMatrix3170 node3170 pivotPermutation3170; decide +kernel
  have hmoment : injectiveMoment H node3170 = injectiveMoment H pivotMatrix3170 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3170 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3170 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3170 (0 : Fin 5)) =
      Sparse.eval value1751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3170 (0 : Fin 5) = raw2197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3170 raw2197; decide +kernel
    rw [heq]
    exact (canonical2197 hH).trans (sound1751 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3170 (1 : Fin 5)) =
      Sparse.eval value1999 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3170 (1 : Fin 5) = raw3333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3170 raw3333; decide +kernel
    rw [heq]
    exact (canonical3333 hH).trans (sound1999 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3170 (2 : Fin 5)) =
      Sparse.eval value2583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3170 (2 : Fin 5) = raw3387 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3170 raw3387; decide +kernel
    rw [heq]
    exact (canonical3387 hH).trans (sound2583 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3170 (3 : Fin 5)) =
      Sparse.eval value2018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3170 (3 : Fin 5) = raw3400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3170 raw3400; decide +kernel
    rw [heq]
    exact (canonical3400 hH).trans (sound2018 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3170 (4 : Fin 5)) =
      Sparse.eval value2784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3170 (4 : Fin 5) = raw3402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3170 raw3402; decide +kernel
    rw [heq]
    exact (canonical3402 hH).trans (sound2784 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3170 + (injectiveMoment H (mergeFirst pivotMatrix3170 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3170 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3170 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3170 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3170 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3170, value1751, value1999, value2018, value2583, value2784, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3171 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3171 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem sound3171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3171 = Sparse.eval value3171 (momentVector H) := by
  have heq : pivotMatrix3171 = (fun u v => node3171 (pivotPermutation3171 u) v) := by apply Matrix.ext; unfold pivotMatrix3171 node3171 pivotPermutation3171; decide +kernel
  have hmoment : injectiveMoment H node3171 = injectiveMoment H pivotMatrix3171 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3171 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3171 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3171 (0 : Fin 5)) =
      Sparse.eval value1765 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3171 (0 : Fin 5) = raw2249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3171 raw2249; decide +kernel
    rw [heq]
    exact (canonical2249 hH).trans (sound1765 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3171 (1 : Fin 5)) =
      Sparse.eval value1503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3171 (1 : Fin 5) = raw3375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3171 raw3375; decide +kernel
    rw [heq]
    exact (canonical3375 hH).trans (sound1503 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3171 (2 : Fin 5)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3171 (2 : Fin 5) = raw3455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3171 raw3455; decide +kernel
    rw [heq]
    exact (canonical3455 hH).trans (sound1032 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3171 (3 : Fin 5)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3171 (3 : Fin 5) = raw3462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3171 raw3462; decide +kernel
    rw [heq]
    exact (canonical3462 hH).trans (sound1032 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3171 (4 : Fin 5)) =
      Sparse.eval value2032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3171 (4 : Fin 5) = raw3463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3171 raw3463; decide +kernel
    rw [heq]
    exact (canonical3463 hH).trans (sound2032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3171 + (injectiveMoment H (mergeFirst pivotMatrix3171 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3171 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3171 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3171 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3171 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3171, value1032, value1503, value1765, value2032, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3172 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3172 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem sound3172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3172 = Sparse.eval value3172 (momentVector H) := by
  have heq : pivotMatrix3172 = (fun u v => node3172 (pivotPermutation3172 u) v) := by apply Matrix.ext; unfold pivotMatrix3172 node3172 pivotPermutation3172; decide +kernel
  have hmoment : injectiveMoment H node3172 = injectiveMoment H pivotMatrix3172 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3172 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3172 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3172 (0 : Fin 5)) =
      Sparse.eval value1767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3172 (0 : Fin 5) = raw2251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3172 raw2251; decide +kernel
    rw [heq]
    exact (canonical2251 hH).trans (sound1767 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3172 (1 : Fin 5)) =
      Sparse.eval value1603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3172 (1 : Fin 5) = raw3376 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3172 raw3376; decide +kernel
    rw [heq]
    exact (canonical3376 hH).trans (sound1603 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3172 (2 : Fin 5)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3172 (2 : Fin 5) = raw3456 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3172 raw3456; decide +kernel
    rw [heq]
    exact (canonical3456 hH).trans (sound769 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3172 (3 : Fin 5)) =
      Sparse.eval value1581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3172 (3 : Fin 5) = raw3467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3172 raw3467; decide +kernel
    rw [heq]
    exact (canonical3467 hH).trans (sound1581 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3172 (4 : Fin 5)) =
      Sparse.eval value2807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3172 (4 : Fin 5) = raw3469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3172 raw3469; decide +kernel
    rw [heq]
    exact (canonical3469 hH).trans (sound2807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3172 + (injectiveMoment H (mergeFirst pivotMatrix3172 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3172 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3172 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3172 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3172 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3172, value1581, value1603, value1767, value2807, value769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3173 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3173 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem sound3173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3173 = Sparse.eval value3173 (momentVector H) := by
  have heq : pivotMatrix3173 = (fun u v => node3173 (pivotPermutation3173 u) v) := by apply Matrix.ext; unfold pivotMatrix3173 node3173 pivotPermutation3173; decide +kernel
  have hmoment : injectiveMoment H node3173 = injectiveMoment H pivotMatrix3173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3173 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3173 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3173 (0 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3173 (0 : Fin 5) = raw2322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3173 raw2322; decide +kernel
    rw [heq]
    exact (canonical2322 hH).trans (sound1786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3173 (1 : Fin 5)) =
      Sparse.eval value2015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3173 (1 : Fin 5) = raw3411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3173 raw3411; decide +kernel
    rw [heq]
    exact (canonical3411 hH).trans (sound2015 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3173 (2 : Fin 5)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3173 (2 : Fin 5) = raw3479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3173 raw3479; decide +kernel
    rw [heq]
    exact (canonical3479 hH).trans (sound1054 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3173 (3 : Fin 5)) =
      Sparse.eval value2613 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3173 (3 : Fin 5) = raw3484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3173 raw3484; decide +kernel
    rw [heq]
    exact (canonical3484 hH).trans (sound2613 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3173 (4 : Fin 5)) =
      Sparse.eval value2745 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3173 (4 : Fin 5) = raw3488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3173 raw3488; decide +kernel
    rw [heq]
    exact (canonical3488 hH).trans (sound2745 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3173 + (injectiveMoment H (mergeFirst pivotMatrix3173 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3173 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3173 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3173 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3173 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3173, value1054, value1786, value2015, value2613, value2745, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3174 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3174 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound3174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3174 = Sparse.eval value3174 (momentVector H) := by
  have heq : pivotMatrix3174 = (fun u v => node3174 (pivotPermutation3174 u) v) := by apply Matrix.ext; unfold pivotMatrix3174 node3174 pivotPermutation3174; decide +kernel
  have hmoment : injectiveMoment H node3174 = injectiveMoment H pivotMatrix3174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3174 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3174 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3174 (0 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3174 (0 : Fin 5) = raw2332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3174 raw2332; decide +kernel
    rw [heq]
    exact (canonical2332 hH).trans (sound1793 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3174 (1 : Fin 5)) =
      Sparse.eval value2021 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3174 (1 : Fin 5) = raw3412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3174 raw3412; decide +kernel
    rw [heq]
    exact (canonical3412 hH).trans (sound2021 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3174 (2 : Fin 5)) =
      Sparse.eval value2609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3174 (2 : Fin 5) = raw3480 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3174 raw3480; decide +kernel
    rw [heq]
    exact (canonical3480 hH).trans (sound2609 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3174 (3 : Fin 5)) =
      Sparse.eval value2023 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3174 (3 : Fin 5) = raw3489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3174 raw3489; decide +kernel
    rw [heq]
    exact (canonical3489 hH).trans (sound2023 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3174 (4 : Fin 5)) =
      Sparse.eval value2759 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3174 (4 : Fin 5) = raw3490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3174 raw3490; decide +kernel
    rw [heq]
    exact (canonical3490 hH).trans (sound2759 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3174 + (injectiveMoment H (mergeFirst pivotMatrix3174 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3174 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3174 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3174 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3174 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3174, value1793, value2021, value2023, value2609, value2759, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3175 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3175 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound3175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3175 = Sparse.eval value3175 (momentVector H) := by
  have heq : pivotMatrix3175 = (fun u v => node3175 (pivotPermutation3175 u) v) := by apply Matrix.ext; unfold pivotMatrix3175 node3175 pivotPermutation3175; decide +kernel
  have hmoment : injectiveMoment H node3175 = injectiveMoment H pivotMatrix3175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3175 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3175 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3175 (0 : Fin 5)) =
      Sparse.eval value2077 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3175 (0 : Fin 5) = raw3726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3175 raw3726; decide +kernel
    rw [heq]
    exact (canonical3726 hH).trans (sound2077 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3175 (1 : Fin 5)) =
      Sparse.eval value1518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3175 (1 : Fin 5) = raw3464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3175 raw3464; decide +kernel
    rw [heq]
    exact (canonical3464 hH).trans (sound1518 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3175 (2 : Fin 5)) =
      Sparse.eval value1517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3175 (2 : Fin 5) = raw3431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3175 raw3431; decide +kernel
    rw [heq]
    exact (canonical3431 hH).trans (sound1517 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3175 (3 : Fin 5)) =
      Sparse.eval value2025 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3175 (3 : Fin 5) = raw3426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3175 raw3426; decide +kernel
    rw [heq]
    exact (canonical3426 hH).trans (sound2025 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3175 (4 : Fin 5)) =
      Sparse.eval value2024 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3175 (4 : Fin 5) = raw3425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3175 raw3425; decide +kernel
    rw [heq]
    exact (canonical3425 hH).trans (sound2024 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3175 + (injectiveMoment H (mergeFirst pivotMatrix3175 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3175 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3175 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3175 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3175 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3175, value1517, value1518, value2024, value2025, value2077, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3176 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3176 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound3176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3176 = Sparse.eval value3176 (momentVector H) := by
  have heq : pivotMatrix3176 = (fun u v => node3176 (pivotPermutation3176 u) v) := by apply Matrix.ext; unfold pivotMatrix3176 node3176 pivotPermutation3176; decide +kernel
  have hmoment : injectiveMoment H node3176 = injectiveMoment H pivotMatrix3176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3176 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3176 (0 : Fin 5)) =
      Sparse.eval value2216 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (0 : Fin 5) = raw4493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw4493; decide +kernel
    rw [heq]
    exact (canonical4493 hH).trans (sound2216 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3176 (1 : Fin 5)) =
      Sparse.eval value2037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (1 : Fin 5) = raw3510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3510; decide +kernel
    rw [heq]
    exact (canonical3510 hH).trans (sound2037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3176 (2 : Fin 5)) =
      Sparse.eval value2029 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (2 : Fin 5) = raw3440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3440; decide +kernel
    rw [heq]
    exact (canonical3440 hH).trans (sound2029 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3176 (3 : Fin 5)) =
      Sparse.eval value2762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (3 : Fin 5) = raw3433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3433; decide +kernel
    rw [heq]
    exact (canonical3433 hH).trans (sound2762 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3176 (4 : Fin 5)) =
      Sparse.eval value2028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (4 : Fin 5) = raw3432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3432; decide +kernel
    rw [heq]
    exact (canonical3432 hH).trans (sound2028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3176 + (injectiveMoment H (mergeFirst pivotMatrix3176 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3176, value2028, value2029, value2037, value2216, value2762, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3177 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3177 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound3177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3177 = Sparse.eval value3177 (momentVector H) := by
  have heq : pivotMatrix3177 = (fun u v => node3177 (pivotPermutation3177 u) v) := by apply Matrix.ext; unfold pivotMatrix3177 node3177 pivotPermutation3177; decide +kernel
  have hmoment : injectiveMoment H node3177 = injectiveMoment H pivotMatrix3177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3177 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3177 (0 : Fin 5)) =
      Sparse.eval value2218 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3177 (0 : Fin 5) = raw4497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3177 raw4497; decide +kernel
    rw [heq]
    exact (canonical4497 hH).trans (sound2218 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3177 (1 : Fin 5)) =
      Sparse.eval value2038 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3177 (1 : Fin 5) = raw3513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3177 raw3513; decide +kernel
    rw [heq]
    exact (canonical3513 hH).trans (sound2038 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3177 (2 : Fin 5)) =
      Sparse.eval value1475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3177 (2 : Fin 5) = raw3443 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3177 raw3443; decide +kernel
    rw [heq]
    exact (canonical3443 hH).trans (sound1475 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3177 (3 : Fin 5)) =
      Sparse.eval value2687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3177 (3 : Fin 5) = raw3438 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3177 raw3438; decide +kernel
    rw [heq]
    exact (canonical3438 hH).trans (sound2687 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3177 (4 : Fin 5)) =
      Sparse.eval value2687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3177 (4 : Fin 5) = raw3437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3177 raw3437; decide +kernel
    rw [heq]
    exact (canonical3437 hH).trans (sound2687 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3177 + (injectiveMoment H (mergeFirst pivotMatrix3177 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3177 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3177 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3177 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3177 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3177, value1475, value2038, value2218, value2687, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3178 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3178 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem sound3178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3178 = Sparse.eval value3178 (momentVector H) := by
  have heq : pivotMatrix3178 = (fun u v => node3178 (pivotPermutation3178 u) v) := by apply Matrix.ext; unfold pivotMatrix3178 node3178 pivotPermutation3178; decide +kernel
  have hmoment : injectiveMoment H node3178 = injectiveMoment H pivotMatrix3178 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3178 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3178 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3178 (0 : Fin 5)) =
      Sparse.eval value1952 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3178 (0 : Fin 5) = raw3111 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3178 raw3111; decide +kernel
    rw [heq]
    exact (canonical3111 hH).trans (sound1952 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3178 (1 : Fin 5)) =
      Sparse.eval value2026 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3178 (1 : Fin 5) = raw3427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3178 raw3427; decide +kernel
    rw [heq]
    exact (canonical3427 hH).trans (sound2026 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3178 (2 : Fin 5)) =
      Sparse.eval value2030 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3178 (2 : Fin 5) = raw3459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3178 raw3459; decide +kernel
    rw [heq]
    exact (canonical3459 hH).trans (sound2030 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3178 (3 : Fin 5)) =
      Sparse.eval value1702 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3178 (3 : Fin 5) = raw3465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3178 raw3465; decide +kernel
    rw [heq]
    exact (canonical3465 hH).trans (sound1702 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3178 (4 : Fin 5)) =
      Sparse.eval value2033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3178 (4 : Fin 5) = raw3466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3178 raw3466; decide +kernel
    rw [heq]
    exact (canonical3466 hH).trans (sound2033 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3178 + (injectiveMoment H (mergeFirst pivotMatrix3178 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3178 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3178 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3178 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3178 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3178, value1702, value1952, value2026, value2030, value2033, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3179 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3179 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem sound3179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3179 = Sparse.eval value3179 (momentVector H) := by
  have heq : pivotMatrix3179 = (fun u v => node3179 (pivotPermutation3179 u) v) := by apply Matrix.ext; unfold pivotMatrix3179 node3179 pivotPermutation3179; decide +kernel
  have hmoment : injectiveMoment H node3179 = injectiveMoment H pivotMatrix3179 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3179 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3179 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3179 (0 : Fin 5)) =
      Sparse.eval value1953 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3179 (0 : Fin 5) = raw3112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3179 raw3112; decide +kernel
    rw [heq]
    exact (canonical3112 hH).trans (sound1953 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3179 (1 : Fin 5)) =
      Sparse.eval value2027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3179 (1 : Fin 5) = raw3428 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3179 raw3428; decide +kernel
    rw [heq]
    exact (canonical3428 hH).trans (sound2027 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3179 (2 : Fin 5)) =
      Sparse.eval value2031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3179 (2 : Fin 5) = raw3460 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3179 raw3460; decide +kernel
    rw [heq]
    exact (canonical3460 hH).trans (sound2031 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3179 (3 : Fin 5)) =
      Sparse.eval value1581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3179 (3 : Fin 5) = raw3467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3179 raw3467; decide +kernel
    rw [heq]
    exact (canonical3467 hH).trans (sound1581 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3179 (4 : Fin 5)) =
      Sparse.eval value2007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3179 (4 : Fin 5) = raw3468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3179 raw3468; decide +kernel
    rw [heq]
    exact (canonical3468 hH).trans (sound2007 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3179 + (injectiveMoment H (mergeFirst pivotMatrix3179 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3179 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3179 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3179 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3179 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3179, value1581, value1953, value2007, value2027, value2031, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3180 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3180 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound3180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3180 = Sparse.eval value3180 (momentVector H) := by
  have heq : pivotMatrix3180 = (fun u v => node3180 (pivotPermutation3180 u) v) := by apply Matrix.ext; unfold pivotMatrix3180 node3180 pivotPermutation3180; decide +kernel
  have hmoment : injectiveMoment H node3180 = injectiveMoment H pivotMatrix3180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3180 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3180 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3180 (0 : Fin 5)) =
      Sparse.eval value1954 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3180 (0 : Fin 5) = raw3120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3180 raw3120; decide +kernel
    rw [heq]
    exact (canonical3120 hH).trans (sound1954 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3180 (1 : Fin 5)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3180 (1 : Fin 5) = raw3475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3180 raw3475; decide +kernel
    rw [heq]
    exact (canonical3475 hH).trans (sound1059 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3180 (2 : Fin 5)) =
      Sparse.eval value2034 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3180 (2 : Fin 5) = raw3481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3180 raw3481; decide +kernel
    rw [heq]
    exact (canonical3481 hH).trans (sound2034 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3180 (3 : Fin 5)) =
      Sparse.eval value2035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3180 (3 : Fin 5) = raw3482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3180 raw3482; decide +kernel
    rw [heq]
    exact (canonical3482 hH).trans (sound2035 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3180 (4 : Fin 5)) =
      Sparse.eval value1839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3180 (4 : Fin 5) = raw3483 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3180 raw3483; decide +kernel
    rw [heq]
    exact (canonical3483 hH).trans (sound1839 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3180 + (injectiveMoment H (mergeFirst pivotMatrix3180 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3180 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3180 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3180 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3180 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3180, value1059, value1839, value1954, value2034, value2035, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3181 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3181 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem sound3181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3181 = Sparse.eval value3181 (momentVector H) := by
  have heq : pivotMatrix3181 = (fun u v => node3181 (pivotPermutation3181 u) v) := by apply Matrix.ext; unfold pivotMatrix3181 node3181 pivotPermutation3181; decide +kernel
  have hmoment : injectiveMoment H node3181 = injectiveMoment H pivotMatrix3181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3181 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3181 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3181 (0 : Fin 5)) =
      Sparse.eval value1956 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3181 (0 : Fin 5) = raw3122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3181 raw3122; decide +kernel
    rw [heq]
    exact (canonical3122 hH).trans (sound1956 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3181 (1 : Fin 5)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3181 (1 : Fin 5) = raw3476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3181 raw3476; decide +kernel
    rw [heq]
    exact (canonical3476 hH).trans (sound1027 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3181 (2 : Fin 5)) =
      Sparse.eval value2035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3181 (2 : Fin 5) = raw3482 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3181 raw3482; decide +kernel
    rw [heq]
    exact (canonical3482 hH).trans (sound2035 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3181 (3 : Fin 5)) =
      Sparse.eval value2035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3181 (3 : Fin 5) = raw3485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3181 raw3485; decide +kernel
    rw [heq]
    exact (canonical3485 hH).trans (sound2035 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3181 (4 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3181 (4 : Fin 5) = raw3487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3181 raw3487; decide +kernel
    rw [heq]
    exact (canonical3487 hH).trans (sound1749 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3181 + (injectiveMoment H (mergeFirst pivotMatrix3181 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3181 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3181 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3181 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3181 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3181, value1027, value1749, value1956, value2035, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3182 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3182 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem sound3182 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3182 = Sparse.eval value3182 (momentVector H) := by
  have heq : pivotMatrix3182 = (fun u v => node3182 (pivotPermutation3182 u) v) := by apply Matrix.ext; unfold pivotMatrix3182 node3182 pivotPermutation3182; decide +kernel
  have hmoment : injectiveMoment H node3182 = injectiveMoment H pivotMatrix3182 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3182 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3182 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3182 (0 : Fin 5)) =
      Sparse.eval value1960 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (0 : Fin 5) = raw3137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3137; decide +kernel
    rw [heq]
    exact (canonical3137 hH).trans (sound1960 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3182 (1 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (1 : Fin 5) = raw3487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3487; decide +kernel
    rw [heq]
    exact (canonical3487 hH).trans (sound1749 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3182 (2 : Fin 5)) =
      Sparse.eval value2036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (2 : Fin 5) = raw3497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3497; decide +kernel
    rw [heq]
    exact (canonical3497 hH).trans (sound2036 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3182 (3 : Fin 5)) =
      Sparse.eval value2036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (3 : Fin 5) = raw3499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3499; decide +kernel
    rw [heq]
    exact (canonical3499 hH).trans (sound2036 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3182 (4 : Fin 5)) =
      Sparse.eval value2001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3182 (4 : Fin 5) = raw3500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3182 raw3500; decide +kernel
    rw [heq]
    exact (canonical3500 hH).trans (sound2001 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3182 + (injectiveMoment H (mergeFirst pivotMatrix3182 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3182 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3182, value1749, value1960, value2001, value2036, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3183 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3183 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound3183 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3183 = Sparse.eval value3183 (momentVector H) := by
  have heq : pivotMatrix3183 = (fun u v => node3183 (pivotPermutation3183 u) v) := by apply Matrix.ext; unfold pivotMatrix3183 node3183 pivotPermutation3183; decide +kernel
  have hmoment : injectiveMoment H node3183 = injectiveMoment H pivotMatrix3183 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3183 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3183 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3183 (0 : Fin 5)) =
      Sparse.eval value1968 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3183 (0 : Fin 5) = raw3168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3183 raw3168; decide +kernel
    rw [heq]
    exact (canonical3168 hH).trans (sound1968 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3183 (1 : Fin 5)) =
      Sparse.eval value2037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3183 (1 : Fin 5) = raw3510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3183 raw3510; decide +kernel
    rw [heq]
    exact (canonical3510 hH).trans (sound2037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3183 (2 : Fin 5)) =
      Sparse.eval value2041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3183 (2 : Fin 5) = raw3523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3183 raw3523; decide +kernel
    rw [heq]
    exact (canonical3523 hH).trans (sound2041 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3183 (3 : Fin 5)) =
      Sparse.eval value1840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3183 (3 : Fin 5) = raw3526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3183 raw3526; decide +kernel
    rw [heq]
    exact (canonical3526 hH).trans (sound1840 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3183 (4 : Fin 5)) =
      Sparse.eval value2043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3183 (4 : Fin 5) = raw3527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3183 raw3527; decide +kernel
    rw [heq]
    exact (canonical3527 hH).trans (sound2043 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3183 + (injectiveMoment H (mergeFirst pivotMatrix3183 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3183 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3183 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3183 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3183 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3183, value1840, value1968, value2037, value2041, value2043, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3184 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3184 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound3184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3184 = Sparse.eval value3184 (momentVector H) := by
  have heq : pivotMatrix3184 = (fun u v => node3184 (pivotPermutation3184 u) v) := by apply Matrix.ext; unfold pivotMatrix3184 node3184 pivotPermutation3184; decide +kernel
  have hmoment : injectiveMoment H node3184 = injectiveMoment H pivotMatrix3184 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3184 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3184 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3184 (0 : Fin 5)) =
      Sparse.eval value1973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3184 (0 : Fin 5) = raw3177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3184 raw3177; decide +kernel
    rw [heq]
    exact (canonical3177 hH).trans (sound1973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3184 (1 : Fin 5)) =
      Sparse.eval value2038 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3184 (1 : Fin 5) = raw3513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3184 raw3513; decide +kernel
    rw [heq]
    exact (canonical3513 hH).trans (sound2038 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3184 (2 : Fin 5)) =
      Sparse.eval value1695 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3184 (2 : Fin 5) = raw3532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3184 raw3532; decide +kernel
    rw [heq]
    exact (canonical3532 hH).trans (sound1695 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3184 (3 : Fin 5)) =
      Sparse.eval value2046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3184 (3 : Fin 5) = raw3535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3184 raw3535; decide +kernel
    rw [heq]
    exact (canonical3535 hH).trans (sound2046 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3184 (4 : Fin 5)) =
      Sparse.eval value2046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3184 (4 : Fin 5) = raw3536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3184 raw3536; decide +kernel
    rw [heq]
    exact (canonical3536 hH).trans (sound2046 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3184 + (injectiveMoment H (mergeFirst pivotMatrix3184 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3184 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3184 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3184 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3184 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3184, value1695, value1973, value2038, value2046, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3185 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3185 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem sound3185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3185 = Sparse.eval value3185 (momentVector H) := by
  have heq : pivotMatrix3185 = (fun u v => node3185 (pivotPermutation3185 u) v) := by apply Matrix.ext; unfold pivotMatrix3185 node3185 pivotPermutation3185; decide +kernel
  have hmoment : injectiveMoment H node3185 = injectiveMoment H pivotMatrix3185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3185 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3185 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3185 (0 : Fin 5)) =
      Sparse.eval value1974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3185 (0 : Fin 5) = raw3188 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3185 raw3188; decide +kernel
    rw [heq]
    exact (canonical3188 hH).trans (sound1974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3185 (1 : Fin 5)) =
      Sparse.eval value2039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3185 (1 : Fin 5) = raw3521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3185 raw3521; decide +kernel
    rw [heq]
    exact (canonical3521 hH).trans (sound2039 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3185 (2 : Fin 5)) =
      Sparse.eval value2039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3185 (2 : Fin 5) = raw3554 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3185 raw3554; decide +kernel
    rw [heq]
    exact (canonical3554 hH).trans (sound2039 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3185 (3 : Fin 5)) =
      Sparse.eval value2047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3185 (3 : Fin 5) = raw3559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3185 raw3559; decide +kernel
    rw [heq]
    exact (canonical3559 hH).trans (sound2047 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3185 (4 : Fin 5)) =
      Sparse.eval value1657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3185 (4 : Fin 5) = raw3560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3185 raw3560; decide +kernel
    rw [heq]
    exact (canonical3560 hH).trans (sound1657 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3185 + (injectiveMoment H (mergeFirst pivotMatrix3185 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3185 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3185 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3185 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3185 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3185, value1657, value1974, value2039, value2047, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3186 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3186 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem sound3186 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3186 = Sparse.eval value3186 (momentVector H) := by
  have heq : pivotMatrix3186 = (fun u v => node3186 (pivotPermutation3186 u) v) := by apply Matrix.ext; unfold pivotMatrix3186 node3186 pivotPermutation3186; decide +kernel
  have hmoment : injectiveMoment H node3186 = injectiveMoment H pivotMatrix3186 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3186 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3186 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3186 (0 : Fin 5)) =
      Sparse.eval value1976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3186 (0 : Fin 5) = raw3190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3186 raw3190; decide +kernel
    rw [heq]
    exact (canonical3190 hH).trans (sound1976 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3186 (1 : Fin 5)) =
      Sparse.eval value2040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3186 (1 : Fin 5) = raw3522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3186 raw3522; decide +kernel
    rw [heq]
    exact (canonical3522 hH).trans (sound2040 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3186 (2 : Fin 5)) =
      Sparse.eval value2040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3186 (2 : Fin 5) = raw3555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3186 raw3555; decide +kernel
    rw [heq]
    exact (canonical3555 hH).trans (sound2040 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3186 (3 : Fin 5)) =
      Sparse.eval value2013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3186 (3 : Fin 5) = raw3561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3186 raw3561; decide +kernel
    rw [heq]
    exact (canonical3561 hH).trans (sound2013 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3186 (4 : Fin 5)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3186 (4 : Fin 5) = raw3562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3186 raw3562; decide +kernel
    rw [heq]
    exact (canonical3562 hH).trans (sound1752 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3186 + (injectiveMoment H (mergeFirst pivotMatrix3186 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3186 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3186 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3186 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3186 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3186, value1752, value1976, value2013, value2040, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3187 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3187 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound3187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3187 = Sparse.eval value3187 (momentVector H) := by
  have heq : pivotMatrix3187 = (fun u v => node3187 (pivotPermutation3187 u) v) := by apply Matrix.ext; unfold pivotMatrix3187 node3187 pivotPermutation3187; decide +kernel
  have hmoment : injectiveMoment H node3187 = injectiveMoment H pivotMatrix3187 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3187 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3187 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3187 (0 : Fin 5)) =
      Sparse.eval value1977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3187 (0 : Fin 5) = raw3191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3187 raw3191; decide +kernel
    rw [heq]
    exact (canonical3191 hH).trans (sound1977 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3187 (1 : Fin 5)) =
      Sparse.eval value2041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3187 (1 : Fin 5) = raw3523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3187 raw3523; decide +kernel
    rw [heq]
    exact (canonical3523 hH).trans (sound2041 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3187 (2 : Fin 5)) =
      Sparse.eval value2041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3187 (2 : Fin 5) = raw3556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3187 raw3556; decide +kernel
    rw [heq]
    exact (canonical3556 hH).trans (sound2041 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3187 (3 : Fin 5)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3187 (3 : Fin 5) = raw3562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3187 raw3562; decide +kernel
    rw [heq]
    exact (canonical3562 hH).trans (sound1752 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3187 (4 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3187 (4 : Fin 5) = raw3563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3187 raw3563; decide +kernel
    rw [heq]
    exact (canonical3563 hH).trans (sound1507 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3187 + (injectiveMoment H (mergeFirst pivotMatrix3187 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3187 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3187 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3187 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3187 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3187, value1507, value1752, value1977, value2041, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3188 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3188 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound3188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3188 = Sparse.eval value3188 (momentVector H) := by
  have heq : pivotMatrix3188 = (fun u v => node3188 (pivotPermutation3188 u) v) := by apply Matrix.ext; unfold pivotMatrix3188 node3188 pivotPermutation3188; decide +kernel
  have hmoment : injectiveMoment H node3188 = injectiveMoment H pivotMatrix3188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3188 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3188 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3188 (0 : Fin 5)) =
      Sparse.eval value1978 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3188 (0 : Fin 5) = raw3192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3188 raw3192; decide +kernel
    rw [heq]
    exact (canonical3192 hH).trans (sound1978 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3188 (1 : Fin 5)) =
      Sparse.eval value2042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3188 (1 : Fin 5) = raw3524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3188 raw3524; decide +kernel
    rw [heq]
    exact (canonical3524 hH).trans (sound2042 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3188 (2 : Fin 5)) =
      Sparse.eval value2042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3188 (2 : Fin 5) = raw3557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3188 raw3557; decide +kernel
    rw [heq]
    exact (canonical3557 hH).trans (sound2042 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3188 (3 : Fin 5)) =
      Sparse.eval value2048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3188 (3 : Fin 5) = raw3564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3188 raw3564; decide +kernel
    rw [heq]
    exact (canonical3564 hH).trans (sound2048 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3188 (4 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3188 (4 : Fin 5) = raw3565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3188 raw3565; decide +kernel
    rw [heq]
    exact (canonical3565 hH).trans (sound1749 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3188 + (injectiveMoment H (mergeFirst pivotMatrix3188 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3188 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3188 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3188 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3188 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3188, value1749, value1978, value2042, value2048, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3189 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3189 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem sound3189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3189 = Sparse.eval value3189 (momentVector H) := by
  have heq : pivotMatrix3189 = (fun u v => node3189 (pivotPermutation3189 u) v) := by apply Matrix.ext; unfold pivotMatrix3189 node3189 pivotPermutation3189; decide +kernel
  have hmoment : injectiveMoment H node3189 = injectiveMoment H pivotMatrix3189 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3189 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3189 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3189 (0 : Fin 5)) =
      Sparse.eval value1980 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3189 (0 : Fin 5) = raw3197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3189 raw3197; decide +kernel
    rw [heq]
    exact (canonical3197 hH).trans (sound1980 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3189 (1 : Fin 5)) =
      Sparse.eval value2043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3189 (1 : Fin 5) = raw3527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3189 raw3527; decide +kernel
    rw [heq]
    exact (canonical3527 hH).trans (sound2043 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3189 (2 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3189 (2 : Fin 5) = raw3563 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3189 raw3563; decide +kernel
    rw [heq]
    exact (canonical3563 hH).trans (sound1507 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3189 (3 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3189 (3 : Fin 5) = raw3568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3189 raw3568; decide +kernel
    rw [heq]
    exact (canonical3568 hH).trans (sound1800 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3189 (4 : Fin 5)) =
      Sparse.eval value2049 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3189 (4 : Fin 5) = raw3569 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3189 raw3569; decide +kernel
    rw [heq]
    exact (canonical3569 hH).trans (sound2049 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3189 + (injectiveMoment H (mergeFirst pivotMatrix3189 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3189 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3189 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3189 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3189 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3189, value1507, value1800, value1980, value2043, value2049, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3190 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3190 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem sound3190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3190 = Sparse.eval value3190 (momentVector H) := by
  have heq : pivotMatrix3190 = (fun u v => node3190 (pivotPermutation3190 u) v) := by apply Matrix.ext; unfold pivotMatrix3190 node3190 pivotPermutation3190; decide +kernel
  have hmoment : injectiveMoment H node3190 = injectiveMoment H pivotMatrix3190 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3190 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3190 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3190 (0 : Fin 5)) =
      Sparse.eval value1982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3190 (0 : Fin 5) = raw3202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3190 raw3202; decide +kernel
    rw [heq]
    exact (canonical3202 hH).trans (sound1982 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3190 (1 : Fin 5)) =
      Sparse.eval value2044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3190 (1 : Fin 5) = raw3530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3190 raw3530; decide +kernel
    rw [heq]
    exact (canonical3530 hH).trans (sound2044 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3190 (2 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3190 (2 : Fin 5) = raw3568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3190 raw3568; decide +kernel
    rw [heq]
    exact (canonical3568 hH).trans (sound1800 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3190 (3 : Fin 5)) =
      Sparse.eval value2015 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3190 (3 : Fin 5) = raw3572 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3190 raw3572; decide +kernel
    rw [heq]
    exact (canonical3572 hH).trans (sound2015 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3190 (4 : Fin 5)) =
      Sparse.eval value2050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3190 (4 : Fin 5) = raw3573 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3190 raw3573; decide +kernel
    rw [heq]
    exact (canonical3573 hH).trans (sound2050 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3190 + (injectiveMoment H (mergeFirst pivotMatrix3190 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3190 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3190 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3190 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3190 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3190, value1800, value1982, value2015, value2044, value2050, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3191 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3191 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem sound3191 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3191 = Sparse.eval value3191 (momentVector H) := by
  have heq : pivotMatrix3191 = (fun u v => node3191 (pivotPermutation3191 u) v) := by apply Matrix.ext; unfold pivotMatrix3191 node3191 pivotPermutation3191; decide +kernel
  have hmoment : injectiveMoment H node3191 = injectiveMoment H pivotMatrix3191 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3191 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3191 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3191 (0 : Fin 5)) =
      Sparse.eval value1986 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3191 (0 : Fin 5) = raw3209 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3191 raw3209; decide +kernel
    rw [heq]
    exact (canonical3209 hH).trans (sound1986 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3191 (1 : Fin 5)) =
      Sparse.eval value2045 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3191 (1 : Fin 5) = raw3534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3191 raw3534; decide +kernel
    rw [heq]
    exact (canonical3534 hH).trans (sound2045 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3191 (2 : Fin 5)) =
      Sparse.eval value1704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3191 (2 : Fin 5) = raw3575 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3191 raw3575; decide +kernel
    rw [heq]
    exact (canonical3575 hH).trans (sound1704 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3191 (3 : Fin 5)) =
      Sparse.eval value2051 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3191 (3 : Fin 5) = raw3578 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3191 raw3578; decide +kernel
    rw [heq]
    exact (canonical3578 hH).trans (sound2051 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3191 (4 : Fin 5)) =
      Sparse.eval value2052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3191 (4 : Fin 5) = raw3579 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3191 raw3579; decide +kernel
    rw [heq]
    exact (canonical3579 hH).trans (sound2052 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3191 + (injectiveMoment H (mergeFirst pivotMatrix3191 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3191 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3191 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3191 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3191 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3191, value1704, value1986, value2045, value2051, value2052, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3192 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3192 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound3192 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3192 = Sparse.eval value3192 (momentVector H) := by
  have heq : pivotMatrix3192 = (fun u v => node3192 (pivotPermutation3192 u) v) := by apply Matrix.ext; unfold pivotMatrix3192 node3192 pivotPermutation3192; decide +kernel
  have hmoment : injectiveMoment H node3192 = injectiveMoment H pivotMatrix3192 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3192 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3192 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3192 (0 : Fin 5)) =
      Sparse.eval value1987 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3192 (0 : Fin 5) = raw3210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3192 raw3210; decide +kernel
    rw [heq]
    exact (canonical3210 hH).trans (sound1987 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3192 (1 : Fin 5)) =
      Sparse.eval value2046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3192 (1 : Fin 5) = raw3535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3192 raw3535; decide +kernel
    rw [heq]
    exact (canonical3535 hH).trans (sound2046 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3192 (2 : Fin 5)) =
      Sparse.eval value1698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3192 (2 : Fin 5) = raw3576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3192 raw3576; decide +kernel
    rw [heq]
    exact (canonical3576 hH).trans (sound1698 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3192 (3 : Fin 5)) =
      Sparse.eval value2053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3192 (3 : Fin 5) = raw3580 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3192 raw3580; decide +kernel
    rw [heq]
    exact (canonical3580 hH).trans (sound2053 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3192 (4 : Fin 5)) =
      Sparse.eval value2054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3192 (4 : Fin 5) = raw3581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3192 raw3581; decide +kernel
    rw [heq]
    exact (canonical3581 hH).trans (sound2054 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3192 + (injectiveMoment H (mergeFirst pivotMatrix3192 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3192 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3192 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3192 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3192 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3192, value1698, value1987, value2046, value2053, value2054, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3193 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3193 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3193 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3193 = Sparse.eval value3193 (momentVector H) := by
  have heq : pivotMatrix3193 = (fun u v => node3193 (pivotPermutation3193 u) v) := by apply Matrix.ext; unfold pivotMatrix3193 node3193 pivotPermutation3193; decide +kernel
  have hmoment : injectiveMoment H node3193 = injectiveMoment H pivotMatrix3193 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3193 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3193 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3193 (0 : Fin 5)) =
      Sparse.eval value2587 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3193 (0 : Fin 5) = raw4642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3193 raw4642; decide +kernel
    rw [heq]
    exact (canonical4642 hH).trans (sound2587 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3193 (1 : Fin 5)) =
      Sparse.eval value2734 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3193 (1 : Fin 5) = raw3705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3193 raw3705; decide +kernel
    rw [heq]
    exact (canonical3705 hH).trans (sound2734 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3193 (2 : Fin 5)) =
      Sparse.eval value2013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3193 (2 : Fin 5) = raw3667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3193 raw3667; decide +kernel
    rw [heq]
    exact (canonical3667 hH).trans (sound2013 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3193 (3 : Fin 5)) =
      Sparse.eval value2057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3193 (3 : Fin 5) = raw3664 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3193 raw3664; decide +kernel
    rw [heq]
    exact (canonical3664 hH).trans (sound2057 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3193 (4 : Fin 5)) =
      Sparse.eval value2057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3193 (4 : Fin 5) = raw3663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3193 raw3663; decide +kernel
    rw [heq]
    exact (canonical3663 hH).trans (sound2057 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3193 + (injectiveMoment H (mergeFirst pivotMatrix3193 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3193 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3193 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3193 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3193 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3193, value2013, value2057, value2587, value2734, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3194 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3194 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound3194 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3194 = Sparse.eval value3194 (momentVector H) := by
  have heq : pivotMatrix3194 = (fun u v => node3194 (pivotPermutation3194 u) v) := by apply Matrix.ext; unfold pivotMatrix3194 node3194 pivotPermutation3194; decide +kernel
  have hmoment : injectiveMoment H node3194 = injectiveMoment H pivotMatrix3194 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3194 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3194 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3194 (0 : Fin 5)) =
      Sparse.eval value1727 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3194 (0 : Fin 5) = raw2156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3194 raw2156; decide +kernel
    rw [heq]
    exact (canonical2156 hH).trans (sound1727 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3194 (1 : Fin 5)) =
      Sparse.eval value1940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3194 (1 : Fin 5) = raw3657 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3194 raw3657; decide +kernel
    rw [heq]
    exact (canonical3657 hH).trans (sound1940 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3194 (2 : Fin 5)) =
      Sparse.eval value2491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3194 (2 : Fin 5) = raw3680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3194 raw3680; decide +kernel
    rw [heq]
    exact (canonical3680 hH).trans (sound2491 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3194 (3 : Fin 5)) =
      Sparse.eval value2062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3194 (3 : Fin 5) = raw3684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3194 raw3684; decide +kernel
    rw [heq]
    exact (canonical3684 hH).trans (sound2062 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3194 (4 : Fin 5)) =
      Sparse.eval value2717 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3194 (4 : Fin 5) = raw3686 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3194 raw3686; decide +kernel
    rw [heq]
    exact (canonical3686 hH).trans (sound2717 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3194 + (injectiveMoment H (mergeFirst pivotMatrix3194 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3194 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3194 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3194 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3194 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3194, value1727, value1940, value2062, value2491, value2717, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3195 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3195 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem sound3195 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3195 = Sparse.eval value3195 (momentVector H) := by
  have heq : pivotMatrix3195 = (fun u v => node3195 (pivotPermutation3195 u) v) := by apply Matrix.ext; unfold pivotMatrix3195 node3195 pivotPermutation3195; decide +kernel
  have hmoment : injectiveMoment H node3195 = injectiveMoment H pivotMatrix3195 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3195 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3195 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3195 (0 : Fin 5)) =
      Sparse.eval value1562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3195 (0 : Fin 5) = raw3353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3195 raw3353; decide +kernel
    rw [heq]
    exact (canonical3353 hH).trans (sound1562 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3195 (1 : Fin 5)) =
      Sparse.eval value2058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3195 (1 : Fin 5) = raw3677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3195 raw3677; decide +kernel
    rw [heq]
    exact (canonical3677 hH).trans (sound2058 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3195 (2 : Fin 5)) =
      Sparse.eval value2060 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3195 (2 : Fin 5) = raw3681 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3195 raw3681; decide +kernel
    rw [heq]
    exact (canonical3681 hH).trans (sound2060 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3195 (3 : Fin 5)) =
      Sparse.eval value2062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3195 (3 : Fin 5) = raw3684 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3195 raw3684; decide +kernel
    rw [heq]
    exact (canonical3684 hH).trans (sound2062 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3195 (4 : Fin 5)) =
      Sparse.eval value2063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3195 (4 : Fin 5) = raw3685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3195 raw3685; decide +kernel
    rw [heq]
    exact (canonical3685 hH).trans (sound2063 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3195 + (injectiveMoment H (mergeFirst pivotMatrix3195 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3195 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3195 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3195 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3195 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3195, value1562, value2058, value2060, value2062, value2063, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3196 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3196 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem sound3196 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3196 = Sparse.eval value3196 (momentVector H) := by
  have heq : pivotMatrix3196 = (fun u v => node3196 (pivotPermutation3196 u) v) := by apply Matrix.ext; unfold pivotMatrix3196 node3196 pivotPermutation3196; decide +kernel
  have hmoment : injectiveMoment H node3196 = injectiveMoment H pivotMatrix3196 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3196 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3196 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3196 (0 : Fin 5)) =
      Sparse.eval value1736 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3196 (0 : Fin 5) = raw2181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3196 raw2181; decide +kernel
    rw [heq]
    exact (canonical2181 hH).trans (sound1736 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3196 (1 : Fin 5)) =
      Sparse.eval value1990 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3196 (1 : Fin 5) = raw3659 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3196 raw3659; decide +kernel
    rw [heq]
    exact (canonical3659 hH).trans (sound1990 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3196 (2 : Fin 5)) =
      Sparse.eval value2059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3196 (2 : Fin 5) = raw3698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3196 raw3698; decide +kernel
    rw [heq]
    exact (canonical3698 hH).trans (sound2059 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3196 (3 : Fin 5)) =
      Sparse.eval value2532 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3196 (3 : Fin 5) = raw3701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3196 raw3701; decide +kernel
    rw [heq]
    exact (canonical3701 hH).trans (sound2532 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3196 (4 : Fin 5)) =
      Sparse.eval value2623 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3196 (4 : Fin 5) = raw3702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3196 raw3702; decide +kernel
    rw [heq]
    exact (canonical3702 hH).trans (sound2623 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3196 + (injectiveMoment H (mergeFirst pivotMatrix3196 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3196 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3196 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3196 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3196 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3196, value1736, value1990, value2059, value2532, value2623, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3197 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3197 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound3197 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3197 = Sparse.eval value3197 (momentVector H) := by
  have heq : pivotMatrix3197 = (fun u v => node3197 (pivotPermutation3197 u) v) := by apply Matrix.ext; unfold pivotMatrix3197 node3197 pivotPermutation3197; decide +kernel
  have hmoment : injectiveMoment H node3197 = injectiveMoment H pivotMatrix3197 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3197 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3197 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3197 (0 : Fin 5)) =
      Sparse.eval value1739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3197 (0 : Fin 5) = raw2182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3197 raw2182; decide +kernel
    rw [heq]
    exact (canonical2182 hH).trans (sound1739 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3197 (1 : Fin 5)) =
      Sparse.eval value1993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3197 (1 : Fin 5) = raw3660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3197 raw3660; decide +kernel
    rw [heq]
    exact (canonical3660 hH).trans (sound1993 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3197 (2 : Fin 5)) =
      Sparse.eval value2532 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3197 (2 : Fin 5) = raw3701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3197 raw3701; decide +kernel
    rw [heq]
    exact (canonical3701 hH).trans (sound2532 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3197 (3 : Fin 5)) =
      Sparse.eval value2070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3197 (3 : Fin 5) = raw3703 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3197 raw3703; decide +kernel
    rw [heq]
    exact (canonical3703 hH).trans (sound2070 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3197 (4 : Fin 5)) =
      Sparse.eval value2744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3197 (4 : Fin 5) = raw3704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3197 raw3704; decide +kernel
    rw [heq]
    exact (canonical3704 hH).trans (sound2744 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3197 + (injectiveMoment H (mergeFirst pivotMatrix3197 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3197 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3197 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3197 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3197 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3197, value1739, value1993, value2070, value2532, value2744, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3198 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3198 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound3198 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3198 = Sparse.eval value3198 (momentVector H) := by
  have heq : pivotMatrix3198 = (fun u v => node3198 (pivotPermutation3198 u) v) := by apply Matrix.ext; unfold pivotMatrix3198 node3198 pivotPermutation3198; decide +kernel
  have hmoment : injectiveMoment H node3198 = injectiveMoment H pivotMatrix3198 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3198 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3198 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3198 (0 : Fin 5)) =
      Sparse.eval value1747 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3198 (0 : Fin 5) = raw2193 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3198 raw2193; decide +kernel
    rw [heq]
    exact (canonical2193 hH).trans (sound1747 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3198 (1 : Fin 5)) =
      Sparse.eval value2056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3198 (1 : Fin 5) = raw3662 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3198 raw3662; decide +kernel
    rw [heq]
    exact (canonical3662 hH).trans (sound2056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3198 (2 : Fin 5)) =
      Sparse.eval value2584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3198 (2 : Fin 5) = raw3711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3198 raw3711; decide +kernel
    rw [heq]
    exact (canonical3711 hH).trans (sound2584 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3198 (3 : Fin 5)) =
      Sparse.eval value2072 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3198 (3 : Fin 5) = raw3713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3198 raw3713; decide +kernel
    rw [heq]
    exact (canonical3713 hH).trans (sound2072 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3198 (4 : Fin 5)) =
      Sparse.eval value2724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3198 (4 : Fin 5) = raw3715 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3198 raw3715; decide +kernel
    rw [heq]
    exact (canonical3715 hH).trans (sound2724 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3198 + (injectiveMoment H (mergeFirst pivotMatrix3198 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3198 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3198 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3198 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3198 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3198, value1747, value2056, value2072, value2584, value2724, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3199 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3199 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 1, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound3199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3199 = Sparse.eval value3199 (momentVector H) := by
  have heq : pivotMatrix3199 = (fun u v => node3199 (pivotPermutation3199 u) v) := by apply Matrix.ext; unfold pivotMatrix3199 node3199 pivotPermutation3199; decide +kernel
  have hmoment : injectiveMoment H node3199 = injectiveMoment H pivotMatrix3199 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3199 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3199 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3199 (0 : Fin 5)) =
      Sparse.eval value1748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3199 (0 : Fin 5) = raw2194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3199 raw2194; decide +kernel
    rw [heq]
    exact (canonical2194 hH).trans (sound1748 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3199 (1 : Fin 5)) =
      Sparse.eval value2057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3199 (1 : Fin 5) = raw3663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3199 raw3663; decide +kernel
    rw [heq]
    exact (canonical3663 hH).trans (sound2057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3199 (2 : Fin 5)) =
      Sparse.eval value2630 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3199 (2 : Fin 5) = raw3712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3199 raw3712; decide +kernel
    rw [heq]
    exact (canonical3712 hH).trans (sound2630 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3199 (3 : Fin 5)) =
      Sparse.eval value2581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3199 (3 : Fin 5) = raw3714 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3199 raw3714; decide +kernel
    rw [heq]
    exact (canonical3714 hH).trans (sound2581 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3199 (4 : Fin 5)) =
      Sparse.eval value2724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3199 (4 : Fin 5) = raw3716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3199 raw3716; decide +kernel
    rw [heq]
    exact (canonical3716 hH).trans (sound2724 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3199 + (injectiveMoment H (mergeFirst pivotMatrix3199 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3199 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3199 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3199 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3199 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3199, value1748, value2057, value2581, value2630, value2724, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
