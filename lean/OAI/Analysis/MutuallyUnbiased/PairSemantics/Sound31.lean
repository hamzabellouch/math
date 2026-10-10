import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical95
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical199
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1984 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1984 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem sound1984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1984 = Sparse.eval value1984 (momentVector H) := by
  have heq : pivotMatrix1984 = (fun u v => node1984 (pivotPermutation1984 u) v) := by apply Matrix.ext; unfold pivotMatrix1984 node1984 pivotPermutation1984; decide +kernel
  have hmoment : injectiveMoment H node1984 = injectiveMoment H pivotMatrix1984 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1984 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1984 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1984 (0 : Fin 4)) =
      Sparse.eval value1067 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1984 (0 : Fin 4) = raw4430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1984 raw4430; decide +kernel
    rw [heq]
    exact (canonical4430 hH).trans (sound1067 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1984 (1 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1984 (1 : Fin 4) = raw3272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1984 raw3272; decide +kernel
    rw [heq]
    exact (canonical3272 hH).trans (sound1066 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1984 (2 : Fin 4)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1984 (2 : Fin 4) = raw3250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1984 raw3250; decide +kernel
    rw [heq]
    exact (canonical3250 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1984 (3 : Fin 4)) =
      Sparse.eval value599 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1984 (3 : Fin 4) = raw3248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1984 raw3248; decide +kernel
    rw [heq]
    exact (canonical3248 hH).trans (sound599 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1984 + (injectiveMoment H (mergeFirst pivotMatrix1984 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1984 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1984 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1984 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1984, value1063, value1066, value1067, value599, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1985 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1985 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem sound1985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1985 = Sparse.eval value1985 (momentVector H) := by
  have heq : pivotMatrix1985 = (fun u v => node1985 (pivotPermutation1985 u) v) := by apply Matrix.ext; unfold pivotMatrix1985 node1985 pivotPermutation1985; decide +kernel
  have hmoment : injectiveMoment H node1985 = injectiveMoment H pivotMatrix1985 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1985 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1985 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1985 (0 : Fin 4)) =
      Sparse.eval value677 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1985 (0 : Fin 4) = raw4431 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1985 raw4431; decide +kernel
    rw [heq]
    exact (canonical4431 hH).trans (sound677 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1985 (1 : Fin 4)) =
      Sparse.eval value491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1985 (1 : Fin 4) = raw3273 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1985 raw3273; decide +kernel
    rw [heq]
    exact (canonical3273 hH).trans (sound491 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1985 (2 : Fin 4)) =
      Sparse.eval value1209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1985 (2 : Fin 4) = raw3252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1985 raw3252; decide +kernel
    rw [heq]
    exact (canonical3252 hH).trans (sound1209 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1985 (3 : Fin 4)) =
      Sparse.eval value797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1985 (3 : Fin 4) = raw3249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1985 raw3249; decide +kernel
    rw [heq]
    exact (canonical3249 hH).trans (sound797 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1985 + (injectiveMoment H (mergeFirst pivotMatrix1985 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1985 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1985 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1985 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1985, value1209, value491, value677, value797, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1986 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1986 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem sound1986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1986 = Sparse.eval value1986 (momentVector H) := by
  have heq : pivotMatrix1986 = (fun u v => node1986 (pivotPermutation1986 u) v) := by apply Matrix.ext; unfold pivotMatrix1986 node1986 pivotPermutation1986; decide +kernel
  have hmoment : injectiveMoment H node1986 = injectiveMoment H pivotMatrix1986 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1986 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1986 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1986 (0 : Fin 4)) =
      Sparse.eval value1020 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1986 (0 : Fin 4) = raw4433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1986 raw4433; decide +kernel
    rw [heq]
    exact (canonical4433 hH).trans (sound1020 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1986 (1 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1986 (1 : Fin 4) = raw3274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1986 raw3274; decide +kernel
    rw [heq]
    exact (canonical3274 hH).trans (sound1155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1986 (2 : Fin 4)) =
      Sparse.eval value934 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1986 (2 : Fin 4) = raw3254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1986 raw3254; decide +kernel
    rw [heq]
    exact (canonical3254 hH).trans (sound934 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1986 (3 : Fin 4)) =
      Sparse.eval value600 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1986 (3 : Fin 4) = raw3253 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1986 raw3253; decide +kernel
    rw [heq]
    exact (canonical3253 hH).trans (sound600 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1986 + (injectiveMoment H (mergeFirst pivotMatrix1986 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1986 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1986 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1986 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1986, value1020, value1155, value600, value934, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1987 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1987 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound1987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1987 = Sparse.eval value1987 (momentVector H) := by
  have heq : pivotMatrix1987 = (fun u v => node1987 (pivotPermutation1987 u) v) := by apply Matrix.ext; unfold pivotMatrix1987 node1987 pivotPermutation1987; decide +kernel
  have hmoment : injectiveMoment H node1987 = injectiveMoment H pivotMatrix1987 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1987 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1987 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1987 (0 : Fin 4)) =
      Sparse.eval value1019 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1987 (0 : Fin 4) = raw4434 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1987 raw4434; decide +kernel
    rw [heq]
    exact (canonical4434 hH).trans (sound1019 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1987 (1 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1987 (1 : Fin 4) = raw3275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1987 raw3275; decide +kernel
    rw [heq]
    exact (canonical3275 hH).trans (sound996 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1987 (2 : Fin 4)) =
      Sparse.eval value1156 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1987 (2 : Fin 4) = raw3256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1987 raw3256; decide +kernel
    rw [heq]
    exact (canonical3256 hH).trans (sound1156 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1987 (3 : Fin 4)) =
      Sparse.eval value934 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1987 (3 : Fin 4) = raw3254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1987 raw3254; decide +kernel
    rw [heq]
    exact (canonical3254 hH).trans (sound934 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1987 + (injectiveMoment H (mergeFirst pivotMatrix1987 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1987 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1987 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1987 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1987, value1019, value1156, value934, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1988 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1988 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![2, 0, -2, 0]]

theorem sound1988 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1988 = Sparse.eval value1988 (momentVector H) := by
  have heq : pivotMatrix1988 = (fun u v => node1988 (pivotPermutation1988 u) v) := by apply Matrix.ext; unfold pivotMatrix1988 node1988 pivotPermutation1988; decide +kernel
  have hmoment : injectiveMoment H node1988 = injectiveMoment H pivotMatrix1988 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1988 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1988 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1988 (0 : Fin 4)) =
      Sparse.eval value577 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1988 (0 : Fin 4) = raw4439 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1988 raw4439; decide +kernel
    rw [heq]
    exact (canonical4439 hH).trans (sound577 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1988 (1 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1988 (1 : Fin 4) = raw3359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1988 raw3359; decide +kernel
    rw [heq]
    exact (canonical3359 hH).trans (sound1164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1988 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1988 (2 : Fin 4) = raw3298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1988 raw3298; decide +kernel
    rw [heq]
    exact (canonical3298 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1988 (3 : Fin 4)) =
      Sparse.eval value399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1988 (3 : Fin 4) = raw3296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1988 raw3296; decide +kernel
    rw [heq]
    exact (canonical3296 hH).trans (sound399 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1988 + (injectiveMoment H (mergeFirst pivotMatrix1988 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1988 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1988 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1988 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1988, value1164, value395, value399, value577, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1989 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1989 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 0, 2], ![1, 0, 3, -4], ![1, 1, -2, 0]]

theorem sound1989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1989 = Sparse.eval value1989 (momentVector H) := by
  have heq : pivotMatrix1989 = (fun u v => node1989 (pivotPermutation1989 u) v) := by apply Matrix.ext; unfold pivotMatrix1989 node1989 pivotPermutation1989; decide +kernel
  have hmoment : injectiveMoment H node1989 = injectiveMoment H pivotMatrix1989 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1989 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1989 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1989 (0 : Fin 4)) =
      Sparse.eval value580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1989 (0 : Fin 4) = raw4440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1989 raw4440; decide +kernel
    rw [heq]
    exact (canonical4440 hH).trans (sound580 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1989 (1 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1989 (1 : Fin 4) = raw3365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1989 raw3365; decide +kernel
    rw [heq]
    exact (canonical3365 hH).trans (sound1155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1989 (2 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1989 (2 : Fin 4) = raw3301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1989 raw3301; decide +kernel
    rw [heq]
    exact (canonical3301 hH).trans (sound396 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1989 (3 : Fin 4)) =
      Sparse.eval value399 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1989 (3 : Fin 4) = raw3299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1989 raw3299; decide +kernel
    rw [heq]
    exact (canonical3299 hH).trans (sound399 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1989 + (injectiveMoment H (mergeFirst pivotMatrix1989 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1989 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1989 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1989 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1989, value1155, value396, value399, value580, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1990 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1990 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem sound1990 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1990 = Sparse.eval value1990 (momentVector H) := by
  have heq : pivotMatrix1990 = (fun u v => node1990 (pivotPermutation1990 u) v) := by apply Matrix.ext; unfold pivotMatrix1990 node1990 pivotPermutation1990; decide +kernel
  have hmoment : injectiveMoment H node1990 = injectiveMoment H pivotMatrix1990 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1990 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1990 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1990 (0 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1990 (0 : Fin 4) = raw3058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1990 raw3058; decide +kernel
    rw [heq]
    exact (canonical3058 hH).trans (sound487 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1990 (1 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1990 (1 : Fin 4) = raw3300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1990 raw3300; decide +kernel
    rw [heq]
    exact (canonical3300 hH).trans (sound976 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1990 (2 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1990 (2 : Fin 4) = raw3320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1990 raw3320; decide +kernel
    rw [heq]
    exact (canonical3320 hH).trans (sound473 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1990 (3 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1990 (3 : Fin 4) = raw3321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1990 raw3321; decide +kernel
    rw [heq]
    exact (canonical3321 hH).trans (sound1309 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1990 + (injectiveMoment H (mergeFirst pivotMatrix1990 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1990 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1990 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1990 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1990, value1309, value473, value487, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1991 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1991 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 1, 2, -4]]

theorem sound1991 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1991 = Sparse.eval value1991 (momentVector H) := by
  have heq : pivotMatrix1991 = (fun u v => node1991 (pivotPermutation1991 u) v) := by apply Matrix.ext; unfold pivotMatrix1991 node1991 pivotPermutation1991; decide +kernel
  have hmoment : injectiveMoment H node1991 = injectiveMoment H pivotMatrix1991 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1991 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1991 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1991 (0 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1991 (0 : Fin 4) = raw7156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1991 raw7156; decide +kernel
    rw [heq]
    exact (canonical7156 hH).trans (sound896 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1991 (1 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1991 (1 : Fin 4) = raw3632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1991 raw3632; decide +kernel
    rw [heq]
    exact (canonical3632 hH).trans (sound450 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1991 (2 : Fin 4)) =
      Sparse.eval value456 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1991 (2 : Fin 4) = raw3319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1991 raw3319; decide +kernel
    rw [heq]
    exact (canonical3319 hH).trans (sound456 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1991 (3 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1991 (3 : Fin 4) = raw3303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1991 raw3303; decide +kernel
    rw [heq]
    exact (canonical3303 hH).trans (sound449 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1991 + (injectiveMoment H (mergeFirst pivotMatrix1991 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1991 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1991 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1991 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1991, value449, value450, value456, value896, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1992 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1992 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -2, 1], ![1, 1, 2, -4]]

theorem sound1992 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1992 = Sparse.eval value1992 (momentVector H) := by
  have heq : pivotMatrix1992 = (fun u v => node1992 (pivotPermutation1992 u) v) := by apply Matrix.ext; unfold pivotMatrix1992 node1992 pivotPermutation1992; decide +kernel
  have hmoment : injectiveMoment H node1992 = injectiveMoment H pivotMatrix1992 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1992 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1992 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1992 (0 : Fin 4)) =
      Sparse.eval value618 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1992 (0 : Fin 4) = raw4441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1992 raw4441; decide +kernel
    rw [heq]
    exact (canonical4441 hH).trans (sound618 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1992 (1 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1992 (1 : Fin 4) = raw3378 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1992 raw3378; decide +kernel
    rw [heq]
    exact (canonical3378 hH).trans (sound774 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1992 (2 : Fin 4)) =
      Sparse.eval value456 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1992 (2 : Fin 4) = raw3319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1992 raw3319; decide +kernel
    rw [heq]
    exact (canonical3319 hH).trans (sound456 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1992 (3 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1992 (3 : Fin 4) = raw3316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1992 raw3316; decide +kernel
    rw [heq]
    exact (canonical3316 hH).trans (sound450 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1992 + (injectiveMoment H (mergeFirst pivotMatrix1992 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1992 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1992 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1992 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1992, value450, value456, value618, value774, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1993 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1993 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound1993 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1993 = Sparse.eval value1993 (momentVector H) := by
  have heq : pivotMatrix1993 = (fun u v => node1993 (pivotPermutation1993 u) v) := by apply Matrix.ext; unfold pivotMatrix1993 node1993 pivotPermutation1993; decide +kernel
  have hmoment : injectiveMoment H node1993 = injectiveMoment H pivotMatrix1993 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1993 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1993 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1993 (0 : Fin 4)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1993 (0 : Fin 4) = raw4442 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1993 raw4442; decide +kernel
    rw [heq]
    exact (canonical4442 hH).trans (sound1249 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1993 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1993 (1 : Fin 4) = raw3379 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1993 raw3379; decide +kernel
    rw [heq]
    exact (canonical3379 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1993 (2 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1993 (2 : Fin 4) = raw3320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1993 raw3320; decide +kernel
    rw [heq]
    exact (canonical3320 hH).trans (sound473 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1993 (3 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1993 (3 : Fin 4) = raw3317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1993 raw3317; decide +kernel
    rw [heq]
    exact (canonical3317 hH).trans (sound1301 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1993 + (injectiveMoment H (mergeFirst pivotMatrix1993 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1993 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1993 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1993 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1993, value1249, value1301, value473, value974, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1994 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1994 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound1994 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1994 = Sparse.eval value1994 (momentVector H) := by
  have heq : pivotMatrix1994 = (fun u v => node1994 (pivotPermutation1994 u) v) := by apply Matrix.ext; unfold pivotMatrix1994 node1994 pivotPermutation1994; decide +kernel
  have hmoment : injectiveMoment H node1994 = injectiveMoment H pivotMatrix1994 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1994 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1994 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1994 (0 : Fin 4)) =
      Sparse.eval value513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1994 (0 : Fin 4) = raw4443 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1994 raw4443; decide +kernel
    rw [heq]
    exact (canonical4443 hH).trans (sound513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1994 (1 : Fin 4)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1994 (1 : Fin 4) = raw3380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1994 raw3380; decide +kernel
    rw [heq]
    exact (canonical3380 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1994 (2 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1994 (2 : Fin 4) = raw3322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1994 raw3322; decide +kernel
    rw [heq]
    exact (canonical3322 hH).trans (sound1309 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1994 (3 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1994 (3 : Fin 4) = raw3318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1994 raw3318; decide +kernel
    rw [heq]
    exact (canonical3318 hH).trans (sound521 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1994 + (injectiveMoment H (mergeFirst pivotMatrix1994 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1994 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1994 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1994 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1994, value1265, value1309, value513, value521, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1995 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1995 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem sound1995 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1995 = Sparse.eval value1995 (momentVector H) := by
  have heq : pivotMatrix1995 = (fun u v => node1995 (pivotPermutation1995 u) v) := by apply Matrix.ext; unfold pivotMatrix1995 node1995 pivotPermutation1995; decide +kernel
  have hmoment : injectiveMoment H node1995 = injectiveMoment H pivotMatrix1995 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1995 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1995 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1995 (0 : Fin 4)) =
      Sparse.eval value620 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1995 (0 : Fin 4) = raw4646 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1995 raw4646; decide +kernel
    rw [heq]
    exact (canonical4646 hH).trans (sound620 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1995 (1 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1995 (1 : Fin 4) = raw3407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1995 raw3407; decide +kernel
    rw [heq]
    exact (canonical3407 hH).trans (sound1008 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1995 (2 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1995 (2 : Fin 4) = raw3323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1995 raw3323; decide +kernel
    rw [heq]
    exact (canonical3323 hH).trans (sound473 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1995 (3 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1995 (3 : Fin 4) = raw3318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1995 raw3318; decide +kernel
    rw [heq]
    exact (canonical3318 hH).trans (sound521 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1995 + (injectiveMoment H (mergeFirst pivotMatrix1995 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1995 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1995 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1995 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1995, value1008, value473, value521, value620, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1996 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1996 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem sound1996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1996 = Sparse.eval value1996 (momentVector H) := by
  have heq : pivotMatrix1996 = (fun u v => node1996 (pivotPermutation1996 u) v) := by apply Matrix.ext; unfold pivotMatrix1996 node1996 pivotPermutation1996; decide +kernel
  have hmoment : injectiveMoment H node1996 = injectiveMoment H pivotMatrix1996 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1996 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1996 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1996 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1996 (0 : Fin 4) = raw7278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1996 raw7278; decide +kernel
    rw [heq]
    exact (canonical7278 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1996 (1 : Fin 4)) =
      Sparse.eval value609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1996 (1 : Fin 4) = raw3633 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1996 raw3633; decide +kernel
    rw [heq]
    exact (canonical3633 hH).trans (sound609 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1996 (2 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1996 (2 : Fin 4) = raw3323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1996 raw3323; decide +kernel
    rw [heq]
    exact (canonical3323 hH).trans (sound473 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1996 (3 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1996 (3 : Fin 4) = raw3311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1996 raw3311; decide +kernel
    rw [heq]
    exact (canonical3311 hH).trans (sound520 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1996 + (injectiveMoment H (mergeFirst pivotMatrix1996 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1996 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1996 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1996 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1996, value1009, value473, value520, value609, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1997 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1997 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound1997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1997 = Sparse.eval value1997 (momentVector H) := by
  have heq : pivotMatrix1997 = (fun u v => node1997 (pivotPermutation1997 u) v) := by apply Matrix.ext; unfold pivotMatrix1997 node1997 pivotPermutation1997; decide +kernel
  have hmoment : injectiveMoment H node1997 = injectiveMoment H pivotMatrix1997 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1997 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1997 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1997 (0 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1997 (0 : Fin 4) = raw7279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1997 raw7279; decide +kernel
    rw [heq]
    exact (canonical7279 hH).trans (sound1008 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1997 (1 : Fin 4)) =
      Sparse.eval value606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1997 (1 : Fin 4) = raw3634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1997 raw3634; decide +kernel
    rw [heq]
    exact (canonical3634 hH).trans (sound606 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1997 (2 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1997 (2 : Fin 4) = raw3324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1997 raw3324; decide +kernel
    rw [heq]
    exact (canonical3324 hH).trans (sound521 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1997 (3 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1997 (3 : Fin 4) = raw3314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1997 raw3314; decide +kernel
    rw [heq]
    exact (canonical3314 hH).trans (sound472 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1997 + (injectiveMoment H (mergeFirst pivotMatrix1997 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1997 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1997 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1997 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1997, value1008, value472, value521, value606, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1998 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1998 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound1998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1998 = Sparse.eval value1998 (momentVector H) := by
  have heq : pivotMatrix1998 = (fun u v => node1998 (pivotPermutation1998 u) v) := by apply Matrix.ext; unfold pivotMatrix1998 node1998 pivotPermutation1998; decide +kernel
  have hmoment : injectiveMoment H node1998 = injectiveMoment H pivotMatrix1998 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1998 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1998 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1998 (0 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (0 : Fin 4) = raw4445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw4445; decide +kernel
    rw [heq]
    exact (canonical4445 hH).trans (sound1304 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1998 (1 : Fin 4)) =
      Sparse.eval value1357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (1 : Fin 4) = raw3396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw3396; decide +kernel
    rw [heq]
    exact (canonical3396 hH).trans (sound1357 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1998 (2 : Fin 4)) =
      Sparse.eval value605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (2 : Fin 4) = raw3338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw3338; decide +kernel
    rw [heq]
    exact (canonical3338 hH).trans (sound605 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1998 (3 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (3 : Fin 4) = raw3329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw3329; decide +kernel
    rw [heq]
    exact (canonical3329 hH).trans (sound1304 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1998 + (injectiveMoment H (mergeFirst pivotMatrix1998 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1998 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1998 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1998 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1998, value1304, value1357, value605, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1999 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1999 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1999 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1999 = Sparse.eval value1999 (momentVector H) := by
  have heq : pivotMatrix1999 = (fun u v => node1999 (pivotPermutation1999 u) v) := by apply Matrix.ext; unfold pivotMatrix1999 node1999 pivotPermutation1999; decide +kernel
  have hmoment : injectiveMoment H node1999 = injectiveMoment H pivotMatrix1999 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1999 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1999 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1999 (0 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1999 (0 : Fin 4) = raw4446 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1999 raw4446; decide +kernel
    rw [heq]
    exact (canonical4446 hH).trans (sound1010 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1999 (1 : Fin 4)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1999 (1 : Fin 4) = raw3403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1999 raw3403; decide +kernel
    rw [heq]
    exact (canonical3403 hH).trans (sound1264 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1999 (2 : Fin 4)) =
      Sparse.eval value606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1999 (2 : Fin 4) = raw3339 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1999 raw3339; decide +kernel
    rw [heq]
    exact (canonical3339 hH).trans (sound606 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1999 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1999 (3 : Fin 4) = raw3336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1999 raw3336; decide +kernel
    rw [heq]
    exact (canonical3336 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1999 + (injectiveMoment H (mergeFirst pivotMatrix1999 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1999 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1999 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1999 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1999, value1010, value1264, value1314, value606, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2000 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2000 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound2000 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2000 = Sparse.eval value2000 (momentVector H) := by
  have heq : pivotMatrix2000 = (fun u v => node2000 (pivotPermutation2000 u) v) := by apply Matrix.ext; unfold pivotMatrix2000 node2000 pivotPermutation2000; decide +kernel
  have hmoment : injectiveMoment H node2000 = injectiveMoment H pivotMatrix2000 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2000 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2000 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2000 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2000 (0 : Fin 4) = raw4447 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2000 raw4447; decide +kernel
    rw [heq]
    exact (canonical4447 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2000 (1 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2000 (1 : Fin 4) = raw3406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2000 raw3406; decide +kernel
    rw [heq]
    exact (canonical3406 hH).trans (sound1241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2000 (2 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2000 (2 : Fin 4) = raw3347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2000 raw3347; decide +kernel
    rw [heq]
    exact (canonical3347 hH).trans (sound608 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2000 (3 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2000 (3 : Fin 4) = raw3345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2000 raw3345; decide +kernel
    rw [heq]
    exact (canonical3345 hH).trans (sound1304 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2000 + (injectiveMoment H (mergeFirst pivotMatrix2000 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2000 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2000 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2000 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2000, value1005, value1241, value1304, value608, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2001 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2001 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound2001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2001 = Sparse.eval value2001 (momentVector H) := by
  have heq : pivotMatrix2001 = (fun u v => node2001 (pivotPermutation2001 u) v) := by apply Matrix.ext; unfold pivotMatrix2001 node2001 pivotPermutation2001; decide +kernel
  have hmoment : injectiveMoment H node2001 = injectiveMoment H pivotMatrix2001 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2001 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2001 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2001 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (0 : Fin 4) = raw4649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw4649; decide +kernel
    rw [heq]
    exact (canonical4649 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2001 (1 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (1 : Fin 4) = raw3415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw3415; decide +kernel
    rw [heq]
    exact (canonical3415 hH).trans (sound1057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2001 (2 : Fin 4)) =
      Sparse.eval value607 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (2 : Fin 4) = raw3342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw3342; decide +kernel
    rw [heq]
    exact (canonical3342 hH).trans (sound607 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2001 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2001 (3 : Fin 4) = raw3336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2001 raw3336; decide +kernel
    rw [heq]
    exact (canonical3336 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2001 + (injectiveMoment H (mergeFirst pivotMatrix2001 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2001 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2001 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2001 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2001, value1057, value1314, value607, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2002 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2002 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -2, 1], ![1, 1, 0, -2]]

theorem sound2002 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2002 = Sparse.eval value2002 (momentVector H) := by
  have heq : pivotMatrix2002 = (fun u v => node2002 (pivotPermutation2002 u) v) := by apply Matrix.ext; unfold pivotMatrix2002 node2002 pivotPermutation2002; decide +kernel
  have hmoment : injectiveMoment H node2002 = injectiveMoment H pivotMatrix2002 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2002 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2002 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2002 (0 : Fin 4)) =
      Sparse.eval value609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2002 (0 : Fin 4) = raw4650 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2002 raw4650; decide +kernel
    rw [heq]
    exact (canonical4650 hH).trans (sound609 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2002 (1 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2002 (1 : Fin 4) = raw3420 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2002 raw3420; decide +kernel
    rw [heq]
    exact (canonical3420 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2002 (2 : Fin 4)) =
      Sparse.eval value606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2002 (2 : Fin 4) = raw3346 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2002 raw3346; decide +kernel
    rw [heq]
    exact (canonical3346 hH).trans (sound606 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2002 (3 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2002 (3 : Fin 4) = raw3343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2002 raw3343; decide +kernel
    rw [heq]
    exact (canonical3343 hH).trans (sound474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2002 + (injectiveMoment H (mergeFirst pivotMatrix2002 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2002 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2002 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2002 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2002, value1010, value474, value606, value609, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2003 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2003 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound2003 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2003 = Sparse.eval value2003 (momentVector H) := by
  have heq : pivotMatrix2003 = (fun u v => node2003 (pivotPermutation2003 u) v) := by apply Matrix.ext; unfold pivotMatrix2003 node2003 pivotPermutation2003; decide +kernel
  have hmoment : injectiveMoment H node2003 = injectiveMoment H pivotMatrix2003 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2003 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2003 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2003 (0 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2003 (0 : Fin 4) = raw4651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2003 raw4651; decide +kernel
    rw [heq]
    exact (canonical4651 hH).trans (sound1000 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2003 (1 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2003 (1 : Fin 4) = raw3421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2003 raw3421; decide +kernel
    rw [heq]
    exact (canonical3421 hH).trans (sound1000 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2003 (2 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2003 (2 : Fin 4) = raw3347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2003 raw3347; decide +kernel
    rw [heq]
    exact (canonical3347 hH).trans (sound608 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2003 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2003 (3 : Fin 4) = raw3344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2003 raw3344; decide +kernel
    rw [heq]
    exact (canonical3344 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2003 + (injectiveMoment H (mergeFirst pivotMatrix2003 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2003 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2003 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2003 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2003, value1000, value1314, value608, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2004 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2004 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem sound2004 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2004 = Sparse.eval value2004 (momentVector H) := by
  have heq : pivotMatrix2004 = (fun u v => node2004 (pivotPermutation2004 u) v) := by apply Matrix.ext; unfold pivotMatrix2004 node2004 pivotPermutation2004; decide +kernel
  have hmoment : injectiveMoment H node2004 = injectiveMoment H pivotMatrix2004 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2004 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2004 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2004 (0 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2004 (0 : Fin 4) = raw7280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2004 raw7280; decide +kernel
    rw [heq]
    exact (canonical7280 hH).trans (sound1057 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2004 (1 : Fin 4)) =
      Sparse.eval value523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2004 (1 : Fin 4) = raw3637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2004 raw3637; decide +kernel
    rw [heq]
    exact (canonical3637 hH).trans (sound523 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2004 (2 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2004 (2 : Fin 4) = raw3348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2004 raw3348; decide +kernel
    rw [heq]
    exact (canonical3348 hH).trans (sound474 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2004 (3 : Fin 4)) =
      Sparse.eval value607 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2004 (3 : Fin 4) = raw3342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2004 raw3342; decide +kernel
    rw [heq]
    exact (canonical3342 hH).trans (sound607 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2004 + (injectiveMoment H (mergeFirst pivotMatrix2004 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2004 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2004 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2004 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2004, value1057, value474, value523, value607, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2005 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2005 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem sound2005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2005 = Sparse.eval value2005 (momentVector H) := by
  have heq : pivotMatrix2005 = (fun u v => node2005 (pivotPermutation2005 u) v) := by apply Matrix.ext; unfold pivotMatrix2005 node2005 pivotPermutation2005; decide +kernel
  have hmoment : injectiveMoment H node2005 = injectiveMoment H pivotMatrix2005 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2005 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2005 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2005 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (0 : Fin 4) = raw6392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw6392; decide +kernel
    rw [heq]
    exact (canonical6392 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2005 (1 : Fin 4)) =
      Sparse.eval value580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (1 : Fin 4) = raw3630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw3630; decide +kernel
    rw [heq]
    exact (canonical3630 hH).trans (sound580 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2005 (2 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (2 : Fin 4) = raw3365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw3365; decide +kernel
    rw [heq]
    exact (canonical3365 hH).trans (sound1155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2005 (3 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (3 : Fin 4) = raw3359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw3359; decide +kernel
    rw [heq]
    exact (canonical3359 hH).trans (sound1164 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2005 + (injectiveMoment H (mergeFirst pivotMatrix2005 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2005 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2005 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2005 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2005, value1155, value1164, value580, value996, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2006 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2006 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem sound2006 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2006 = Sparse.eval value2006 (momentVector H) := by
  have heq : pivotMatrix2006 = (fun u v => node2006 (pivotPermutation2006 u) v) := by apply Matrix.ext; unfold pivotMatrix2006 node2006 pivotPermutation2006; decide +kernel
  have hmoment : injectiveMoment H node2006 = injectiveMoment H pivotMatrix2006 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2006 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2006 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2006 (0 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2006 (0 : Fin 4) = raw6393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2006 raw6393; decide +kernel
    rw [heq]
    exact (canonical6393 hH).trans (sound997 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2006 (1 : Fin 4)) =
      Sparse.eval value577 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2006 (1 : Fin 4) = raw3631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2006 raw3631; decide +kernel
    rw [heq]
    exact (canonical3631 hH).trans (sound577 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2006 (2 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2006 (2 : Fin 4) = raw3366 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2006 raw3366; decide +kernel
    rw [heq]
    exact (canonical3366 hH).trans (sound1155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2006 (3 : Fin 4)) =
      Sparse.eval value401 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2006 (3 : Fin 4) = raw3361 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2006 raw3361; decide +kernel
    rw [heq]
    exact (canonical3361 hH).trans (sound401 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2006 + (injectiveMoment H (mergeFirst pivotMatrix2006 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2006 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2006 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2006 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2006, value1155, value401, value577, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2007 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2007 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem sound2007 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2007 = Sparse.eval value2007 (momentVector H) := by
  have heq : pivotMatrix2007 = (fun u v => node2007 (pivotPermutation2007 u) v) := by apply Matrix.ext; unfold pivotMatrix2007 node2007 pivotPermutation2007; decide +kernel
  have hmoment : injectiveMoment H node2007 = injectiveMoment H pivotMatrix2007 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2007 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2007 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2007 (0 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2007 (0 : Fin 4) = raw1767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2007 raw1767; decide +kernel
    rw [heq]
    exact (canonical1767 hH).trans (sound1352 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2007 (1 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2007 (1 : Fin 4) = raw3320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2007 raw3320; decide +kernel
    rw [heq]
    exact (canonical3320 hH).trans (sound473 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2007 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2007 (2 : Fin 4) = raw3405 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2007 raw3405; decide +kernel
    rw [heq]
    exact (canonical3405 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2007 (3 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2007 (3 : Fin 4) = raw3408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2007 raw3408; decide +kernel
    rw [heq]
    exact (canonical3408 hH).trans (sound1008 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2007 + (injectiveMoment H (mergeFirst pivotMatrix2007 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2007 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2007 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2007 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2007, value1008, value1352, value473, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2008 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2008 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

theorem sound2008 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2008 = Sparse.eval value2008 (momentVector H) := by
  have heq : pivotMatrix2008 = (fun u v => node2008 (pivotPermutation2008 u) v) := by apply Matrix.ext; unfold pivotMatrix2008 node2008 pivotPermutation2008; decide +kernel
  have hmoment : injectiveMoment H node2008 = injectiveMoment H pivotMatrix2008 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2008 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2008 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2008 (0 : Fin 4)) =
      Sparse.eval value480 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (0 : Fin 4) = raw1965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw1965; decide +kernel
    rw [heq]
    exact (canonical1965 hH).trans (sound480 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2008 (1 : Fin 4)) =
      Sparse.eval value602 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (1 : Fin 4) = raw3417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw3417; decide +kernel
    rw [heq]
    exact (canonical3417 hH).trans (sound602 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2008 (2 : Fin 4)) =
      Sparse.eval value1322 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (2 : Fin 4) = raw3496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw3496; decide +kernel
    rw [heq]
    exact (canonical3496 hH).trans (sound1322 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2008 (3 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2008 (3 : Fin 4) = raw3504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2008 raw3504; decide +kernel
    rw [heq]
    exact (canonical3504 hH).trans (sound591 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2008 + (injectiveMoment H (mergeFirst pivotMatrix2008 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2008 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2008 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2008 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2008, value1322, value480, value591, value602, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2009 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2009 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem sound2009 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2009 = Sparse.eval value2009 (momentVector H) := by
  have heq : pivotMatrix2009 = (fun u v => node2009 (pivotPermutation2009 u) v) := by apply Matrix.ext; unfold pivotMatrix2009 node2009 pivotPermutation2009; decide +kernel
  have hmoment : injectiveMoment H node2009 = injectiveMoment H pivotMatrix2009 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2009 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2009 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2009 (0 : Fin 4)) =
      Sparse.eval value492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2009 (0 : Fin 4) = raw2089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2009 raw2089; decide +kernel
    rw [heq]
    exact (canonical2089 hH).trans (sound492 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2009 (1 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2009 (1 : Fin 4) = raw3508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2009 raw3508; decide +kernel
    rw [heq]
    exact (canonical3508 hH).trans (sound975 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2009 (2 : Fin 4)) =
      Sparse.eval value590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2009 (2 : Fin 4) = raw3600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2009 raw3600; decide +kernel
    rw [heq]
    exact (canonical3600 hH).trans (sound590 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2009 (3 : Fin 4)) =
      Sparse.eval value1215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2009 (3 : Fin 4) = raw3603 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2009 raw3603; decide +kernel
    rw [heq]
    exact (canonical3603 hH).trans (sound1215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2009 + (injectiveMoment H (mergeFirst pivotMatrix2009 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2009 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2009 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2009 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2009, value1215, value492, value590, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2010 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2010 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem sound2010 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2010 = Sparse.eval value2010 (momentVector H) := by
  have heq : pivotMatrix2010 = (fun u v => node2010 (pivotPermutation2010 u) v) := by apply Matrix.ext; unfold pivotMatrix2010 node2010 pivotPermutation2010; decide +kernel
  have hmoment : injectiveMoment H node2010 = injectiveMoment H pivotMatrix2010 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2010 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2010 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2010 (0 : Fin 4)) =
      Sparse.eval value1106 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2010 (0 : Fin 4) = raw2093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2010 raw2093; decide +kernel
    rw [heq]
    exact (canonical2093 hH).trans (sound1106 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2010 (1 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2010 (1 : Fin 4) = raw3509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2010 raw3509; decide +kernel
    rw [heq]
    exact (canonical3509 hH).trans (sound979 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2010 (2 : Fin 4)) =
      Sparse.eval value462 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2010 (2 : Fin 4) = raw3605 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2010 raw3605; decide +kernel
    rw [heq]
    exact (canonical3605 hH).trans (sound462 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2010 (3 : Fin 4)) =
      Sparse.eval value1175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2010 (3 : Fin 4) = raw3608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2010 raw3608; decide +kernel
    rw [heq]
    exact (canonical3608 hH).trans (sound1175 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2010 + (injectiveMoment H (mergeFirst pivotMatrix2010 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2010 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2010 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2010 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2010, value1106, value1175, value462, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2011 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2011 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2011 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2011 = Sparse.eval value2011 (momentVector H) := by
  have heq : pivotMatrix2011 = (fun u v => node2011 (pivotPermutation2011 u) v) := by apply Matrix.ext; unfold pivotMatrix2011 node2011 pivotPermutation2011; decide +kernel
  have hmoment : injectiveMoment H node2011 = injectiveMoment H pivotMatrix2011 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2011 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2011 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2011 (0 : Fin 4)) =
      Sparse.eval value1158 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (0 : Fin 4) = raw2096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw2096; decide +kernel
    rw [heq]
    exact (canonical2096 hH).trans (sound1158 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2011 (1 : Fin 4)) =
      Sparse.eval value1300 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (1 : Fin 4) = raw3517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw3517; decide +kernel
    rw [heq]
    exact (canonical3517 hH).trans (sound1300 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2011 (2 : Fin 4)) =
      Sparse.eval value461 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (2 : Fin 4) = raw3611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw3611; decide +kernel
    rw [heq]
    exact (canonical3611 hH).trans (sound461 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2011 (3 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2011 (3 : Fin 4) = raw3615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2011 raw3615; decide +kernel
    rw [heq]
    exact (canonical3615 hH).trans (sound1313 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2011 + (injectiveMoment H (mergeFirst pivotMatrix2011 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2011 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2011 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2011 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2011, value1158, value1300, value1313, value461, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2012 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2012 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem sound2012 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2012 = Sparse.eval value2012 (momentVector H) := by
  have heq : pivotMatrix2012 = (fun u v => node2012 (pivotPermutation2012 u) v) := by apply Matrix.ext; unfold pivotMatrix2012 node2012 pivotPermutation2012; decide +kernel
  have hmoment : injectiveMoment H node2012 = injectiveMoment H pivotMatrix2012 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2012 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2012 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2012 (0 : Fin 4)) =
      Sparse.eval value494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2012 (0 : Fin 4) = raw2097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2012 raw2097; decide +kernel
    rw [heq]
    exact (canonical2097 hH).trans (sound494 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2012 (1 : Fin 4)) =
      Sparse.eval value1318 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2012 (1 : Fin 4) = raw3518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2012 raw3518; decide +kernel
    rw [heq]
    exact (canonical3518 hH).trans (sound1318 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2012 (2 : Fin 4)) =
      Sparse.eval value589 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2012 (2 : Fin 4) = raw3612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2012 raw3612; decide +kernel
    rw [heq]
    exact (canonical3612 hH).trans (sound589 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2012 (3 : Fin 4)) =
      Sparse.eval value603 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2012 (3 : Fin 4) = raw3616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2012 raw3616; decide +kernel
    rw [heq]
    exact (canonical3616 hH).trans (sound603 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2012 + (injectiveMoment H (mergeFirst pivotMatrix2012 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2012 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2012 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2012 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2012, value1318, value494, value589, value603, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2013 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2013 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem sound2013 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2013 = Sparse.eval value2013 (momentVector H) := by
  have heq : pivotMatrix2013 = (fun u v => node2013 (pivotPermutation2013 u) v) := by apply Matrix.ext; unfold pivotMatrix2013 node2013 pivotPermutation2013; decide +kernel
  have hmoment : injectiveMoment H node2013 = injectiveMoment H pivotMatrix2013 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2013 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2013 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2013 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2013 (0 : Fin 4) = raw2201 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2013 raw2201; decide +kernel
    rw [heq]
    exact (canonical2201 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2013 (1 : Fin 4)) =
      Sparse.eval value606 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2013 (1 : Fin 4) = raw3339 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2013 raw3339; decide +kernel
    rw [heq]
    exact (canonical3339 hH).trans (sound606 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2013 (2 : Fin 4)) =
      Sparse.eval value1264 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2013 (2 : Fin 4) = raw3403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2013 raw3403; decide +kernel
    rw [heq]
    exact (canonical3403 hH).trans (sound1264 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2013 (3 : Fin 4)) =
      Sparse.eval value1008 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2013 (3 : Fin 4) = raw3404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2013 raw3404; decide +kernel
    rw [heq]
    exact (canonical3404 hH).trans (sound1008 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2013 + (injectiveMoment H (mergeFirst pivotMatrix2013 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2013 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2013 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2013 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2013, value1008, value1264, value1309, value606, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2014 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2014 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem sound2014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2014 = Sparse.eval value2014 (momentVector H) := by
  have heq : pivotMatrix2014 = (fun u v => node2014 (pivotPermutation2014 u) v) := by apply Matrix.ext; unfold pivotMatrix2014 node2014 pivotPermutation2014; decide +kernel
  have hmoment : injectiveMoment H node2014 = injectiveMoment H pivotMatrix2014 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2014 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2014 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2014 (0 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (0 : Fin 4) = raw2204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw2204; decide +kernel
    rw [heq]
    exact (canonical2204 hH).trans (sound1360 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2014 (1 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (1 : Fin 4) = raw3347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw3347; decide +kernel
    rw [heq]
    exact (canonical3347 hH).trans (sound608 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2014 (2 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (2 : Fin 4) = raw3406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw3406; decide +kernel
    rw [heq]
    exact (canonical3406 hH).trans (sound1241 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2014 (3 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (3 : Fin 4) = raw3409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw3409; decide +kernel
    rw [heq]
    exact (canonical3409 hH).trans (sound1241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2014 + (injectiveMoment H (mergeFirst pivotMatrix2014 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2014 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2014 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2014 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2014, value1241, value1360, value608, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2015 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2015 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem sound2015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2015 = Sparse.eval value2015 (momentVector H) := by
  have heq : pivotMatrix2015 = (fun u v => node2015 (pivotPermutation2015 u) v) := by apply Matrix.ext; unfold pivotMatrix2015 node2015 pivotPermutation2015; decide +kernel
  have hmoment : injectiveMoment H node2015 = injectiveMoment H pivotMatrix2015 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2015 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2015 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2015 (0 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2015 (0 : Fin 4) = raw2349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2015 raw2349; decide +kernel
    rw [heq]
    exact (canonical2349 hH).trans (sound1058 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2015 (1 : Fin 4)) =
      Sparse.eval value609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2015 (1 : Fin 4) = raw3418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2015 raw3418; decide +kernel
    rw [heq]
    exact (canonical3418 hH).trans (sound609 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2015 (2 : Fin 4)) =
      Sparse.eval value1054 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2015 (2 : Fin 4) = raw3491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2015 raw3491; decide +kernel
    rw [heq]
    exact (canonical3491 hH).trans (sound1054 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2015 (3 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2015 (3 : Fin 4) = raw3493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2015 raw3493; decide +kernel
    rw [heq]
    exact (canonical3493 hH).trans (sound1057 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2015 + (injectiveMoment H (mergeFirst pivotMatrix2015 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2015 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2015 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2015 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2015, value1054, value1057, value1058, value609, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2016 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2016 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound2016 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2016 = Sparse.eval value2016 (momentVector H) := by
  have heq : pivotMatrix2016 = (fun u v => node2016 (pivotPermutation2016 u) v) := by apply Matrix.ext; unfold pivotMatrix2016 node2016 pivotPermutation2016; decide +kernel
  have hmoment : injectiveMoment H node2016 = injectiveMoment H pivotMatrix2016 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2016 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2016 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2016 (0 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2016 (0 : Fin 4) = raw2433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2016 raw2433; decide +kernel
    rw [heq]
    exact (canonical2433 hH).trans (sound1123 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2016 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2016 (1 : Fin 4) = raw3477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2016 raw3477; decide +kernel
    rw [heq]
    exact (canonical3477 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2016 (2 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2016 (2 : Fin 4) = raw3584 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2016 raw3584; decide +kernel
    rw [heq]
    exact (canonical3584 hH).trans (sound946 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2016 (3 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2016 (3 : Fin 4) = raw3587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2016 raw3587; decide +kernel
    rw [heq]
    exact (canonical3587 hH).trans (sound1079 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2016 + (injectiveMoment H (mergeFirst pivotMatrix2016 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2016 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2016 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2016 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2016, value1079, value1123, value176, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2017 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2017 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2017 = Sparse.eval value2017 (momentVector H) := by
  have heq : pivotMatrix2017 = (fun u v => node2017 (pivotPermutation2017 u) v) := by apply Matrix.ext; unfold pivotMatrix2017 node2017 pivotPermutation2017; decide +kernel
  have hmoment : injectiveMoment H node2017 = injectiveMoment H pivotMatrix2017 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2017 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2017 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2017 (0 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2017 (0 : Fin 4) = raw2435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2017 raw2435; decide +kernel
    rw [heq]
    exact (canonical2435 hH).trans (sound1096 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2017 (1 : Fin 4)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2017 (1 : Fin 4) = raw3478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2017 raw3478; decide +kernel
    rw [heq]
    exact (canonical3478 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2017 (2 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2017 (2 : Fin 4) = raw3585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2017 raw3585; decide +kernel
    rw [heq]
    exact (canonical3585 hH).trans (sound1005 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2017 (3 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2017 (3 : Fin 4) = raw3588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2017 raw3588; decide +kernel
    rw [heq]
    exact (canonical3588 hH).trans (sound1241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2017 + (injectiveMoment H (mergeFirst pivotMatrix2017 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2017 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2017 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2017 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2017, value1005, value1096, value1241, value227, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2018 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2018 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound2018 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2018 = Sparse.eval value2018 (momentVector H) := by
  have heq : pivotMatrix2018 = (fun u v => node2018 (pivotPermutation2018 u) v) := by apply Matrix.ext; unfold pivotMatrix2018 node2018 pivotPermutation2018; decide +kernel
  have hmoment : injectiveMoment H node2018 = injectiveMoment H pivotMatrix2018 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2018 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2018 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2018 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2018 (0 : Fin 4) = raw2459 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2018 raw2459; decide +kernel
    rw [heq]
    exact (canonical2459 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2018 (1 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2018 (1 : Fin 4) = raw3494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2018 raw3494; decide +kernel
    rw [heq]
    exact (canonical3494 hH).trans (sound1000 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2018 (2 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2018 (2 : Fin 4) = raw3591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2018 raw3591; decide +kernel
    rw [heq]
    exact (canonical3591 hH).trans (sound1010 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2018 (3 : Fin 4)) =
      Sparse.eval value1242 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2018 (3 : Fin 4) = raw3594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2018 raw3594; decide +kernel
    rw [heq]
    exact (canonical3594 hH).trans (sound1242 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2018 + (injectiveMoment H (mergeFirst pivotMatrix2018 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2018 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2018 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2018 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2018, value1000, value1010, value1078, value1242, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2019 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2019 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem sound2019 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2019 = Sparse.eval value2019 (momentVector H) := by
  have heq : pivotMatrix2019 = (fun u v => node2019 (pivotPermutation2019 u) v) := by apply Matrix.ext; unfold pivotMatrix2019 node2019 pivotPermutation2019; decide +kernel
  have hmoment : injectiveMoment H node2019 = injectiveMoment H pivotMatrix2019 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2019 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2019 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2019 (0 : Fin 4)) =
      Sparse.eval value515 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2019 (0 : Fin 4) = raw2472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2019 raw2472; decide +kernel
    rw [heq]
    exact (canonical2472 hH).trans (sound515 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2019 (1 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2019 (1 : Fin 4) = raw3508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2019 raw3508; decide +kernel
    rw [heq]
    exact (canonical3508 hH).trans (sound975 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2019 (2 : Fin 4)) =
      Sparse.eval value612 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2019 (2 : Fin 4) = raw3597 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2019 raw3597; decide +kernel
    rw [heq]
    exact (canonical3597 hH).trans (sound612 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2019 (3 : Fin 4)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2019 (3 : Fin 4) = raw3599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2019 raw3599; decide +kernel
    rw [heq]
    exact (canonical3599 hH).trans (sound1058 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2019 + (injectiveMoment H (mergeFirst pivotMatrix2019 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2019 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2019 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2019 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2019, value1058, value515, value612, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2020 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2020 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem sound2020 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2020 = Sparse.eval value2020 (momentVector H) := by
  have heq : pivotMatrix2020 = (fun u v => node2020 (pivotPermutation2020 u) v) := by apply Matrix.ext; unfold pivotMatrix2020 node2020 pivotPermutation2020; decide +kernel
  have hmoment : injectiveMoment H node2020 = injectiveMoment H pivotMatrix2020 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2020 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2020 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2020 (0 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (0 : Fin 4) = raw2478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw2478; decide +kernel
    rw [heq]
    exact (canonical2478 hH).trans (sound1018 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2020 (1 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (1 : Fin 4) = raw3509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw3509; decide +kernel
    rw [heq]
    exact (canonical3509 hH).trans (sound979 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2020 (2 : Fin 4)) =
      Sparse.eval value590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (2 : Fin 4) = raw3600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw3600; decide +kernel
    rw [heq]
    exact (canonical3600 hH).trans (sound590 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2020 (3 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (3 : Fin 4) = raw3602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw3602; decide +kernel
    rw [heq]
    exact (canonical3602 hH).trans (sound807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2020 + (injectiveMoment H (mergeFirst pivotMatrix2020 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2020 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2020 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2020 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2020, value1018, value590, value807, value979, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2021 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2021 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound2021 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2021 = Sparse.eval value2021 (momentVector H) := by
  have heq : pivotMatrix2021 = (fun u v => node2021 (pivotPermutation2021 u) v) := by apply Matrix.ext; unfold pivotMatrix2021 node2021 pivotPermutation2021; decide +kernel
  have hmoment : injectiveMoment H node2021 = injectiveMoment H pivotMatrix2021 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2021 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2021 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2021 (0 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2021 (0 : Fin 4) = raw4692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2021 raw4692; decide +kernel
    rw [heq]
    exact (canonical4692 hH).trans (sound1000 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2021 (1 : Fin 4)) =
      Sparse.eval value1057 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2021 (1 : Fin 4) = raw3507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2021 raw3507; decide +kernel
    rw [heq]
    exact (canonical3507 hH).trans (sound1057 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2021 (2 : Fin 4)) =
      Sparse.eval value1002 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2021 (2 : Fin 4) = raw3422 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2021 raw3422; decide +kernel
    rw [heq]
    exact (canonical3422 hH).trans (sound1002 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2021 (3 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2021 (3 : Fin 4) = raw3419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2021 raw3419; decide +kernel
    rw [heq]
    exact (canonical3419 hH).trans (sound1010 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2021 + (injectiveMoment H (mergeFirst pivotMatrix2021 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2021 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2021 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2021 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2021, value1000, value1002, value1010, value1057, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2022 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2022 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -3, 1]]

theorem sound2022 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2022 = Sparse.eval value2022 (momentVector H) := by
  have heq : pivotMatrix2022 = (fun u v => node2022 (pivotPermutation2022 u) v) := by apply Matrix.ext; unfold pivotMatrix2022 node2022 pivotPermutation2022; decide +kernel
  have hmoment : injectiveMoment H node2022 = injectiveMoment H pivotMatrix2022 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2022 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2022 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2022 (0 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2022 (0 : Fin 4) = raw6413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2022 raw6413; decide +kernel
    rw [heq]
    exact (canonical6413 hH).trans (sound943 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2022 (1 : Fin 4)) =
      Sparse.eval value612 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2022 (1 : Fin 4) = raw3635 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2022 raw3635; decide +kernel
    rw [heq]
    exact (canonical3635 hH).trans (sound612 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2022 (2 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2022 (2 : Fin 4) = raw3423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2022 raw3423; decide +kernel
    rw [heq]
    exact (canonical3423 hH).trans (sound944 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2022 (3 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2022 (3 : Fin 4) = raw3416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2022 raw3416; decide +kernel
    rw [heq]
    exact (canonical3416 hH).trans (sound1235 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2022 + (injectiveMoment H (mergeFirst pivotMatrix2022 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2022 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2022 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2022 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2022, value1235, value612, value943, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2023 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2023 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem sound2023 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2023 = Sparse.eval value2023 (momentVector H) := by
  have heq : pivotMatrix2023 = (fun u v => node2023 (pivotPermutation2023 u) v) := by apply Matrix.ext; unfold pivotMatrix2023 node2023 pivotPermutation2023; decide +kernel
  have hmoment : injectiveMoment H node2023 = injectiveMoment H pivotMatrix2023 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2023 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2023 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2023 (0 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (0 : Fin 4) = raw6415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw6415; decide +kernel
    rw [heq]
    exact (canonical6415 hH).trans (sound1009 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2023 (1 : Fin 4)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (1 : Fin 4) = raw3636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw3636; decide +kernel
    rw [heq]
    exact (canonical3636 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2023 (2 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (2 : Fin 4) = raw3424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw3424; decide +kernel
    rw [heq]
    exact (canonical3424 hH).trans (sound1000 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2023 (3 : Fin 4)) =
      Sparse.eval value609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2023 (3 : Fin 4) = raw3418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2023 raw3418; decide +kernel
    rw [heq]
    exact (canonical3418 hH).trans (sound609 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2023 + (injectiveMoment H (mergeFirst pivotMatrix2023 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2023 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2023 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2023 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2023, value1000, value1009, value1010, value609, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2024 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2024 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

theorem sound2024 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2024 = Sparse.eval value2024 (momentVector H) := by
  have heq : pivotMatrix2024 = (fun u v => node2024 (pivotPermutation2024 u) v) := by apply Matrix.ext; unfold pivotMatrix2024 node2024 pivotPermutation2024; decide +kernel
  have hmoment : injectiveMoment H node2024 = injectiveMoment H pivotMatrix2024 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2024 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2024 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2024 (0 : Fin 4)) =
      Sparse.eval value1266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2024 (0 : Fin 4) = raw4494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2024 raw4494; decide +kernel
    rw [heq]
    exact (canonical4494 hH).trans (sound1266 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2024 (1 : Fin 4)) =
      Sparse.eval value1271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2024 (1 : Fin 4) = raw3511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2024 raw3511; decide +kernel
    rw [heq]
    exact (canonical3511 hH).trans (sound1271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2024 (2 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2024 (2 : Fin 4) = raw3441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2024 raw3441; decide +kernel
    rw [heq]
    exact (canonical3441 hH).trans (sound406 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2024 (3 : Fin 4)) =
      Sparse.eval value1285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2024 (3 : Fin 4) = raw3435 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2024 raw3435; decide +kernel
    rw [heq]
    exact (canonical3435 hH).trans (sound1285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2024 + (injectiveMoment H (mergeFirst pivotMatrix2024 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2024 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2024 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2024 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2024, value1266, value1271, value1285, value406, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2025 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2025 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem sound2025 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2025 = Sparse.eval value2025 (momentVector H) := by
  have heq : pivotMatrix2025 = (fun u v => node2025 (pivotPermutation2025 u) v) := by apply Matrix.ext; unfold pivotMatrix2025 node2025 pivotPermutation2025; decide +kernel
  have hmoment : injectiveMoment H node2025 = injectiveMoment H pivotMatrix2025 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2025 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2025 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2025 (0 : Fin 4)) =
      Sparse.eval value681 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2025 (0 : Fin 4) = raw4496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2025 raw4496; decide +kernel
    rw [heq]
    exact (canonical4496 hH).trans (sound681 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2025 (1 : Fin 4)) =
      Sparse.eval value610 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2025 (1 : Fin 4) = raw3512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2025 raw3512; decide +kernel
    rw [heq]
    exact (canonical3512 hH).trans (sound610 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2025 (2 : Fin 4)) =
      Sparse.eval value412 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2025 (2 : Fin 4) = raw3442 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2025 raw3442; decide +kernel
    rw [heq]
    exact (canonical3442 hH).trans (sound412 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2025 (3 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2025 (3 : Fin 4) = raw3436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2025 raw3436; decide +kernel
    rw [heq]
    exact (canonical3436 hH).trans (sound1059 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2025 + (injectiveMoment H (mergeFirst pivotMatrix2025 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2025 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2025 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2025 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2025, value1059, value412, value610, value681, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2026 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2026 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem sound2026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2026 = Sparse.eval value2026 (momentVector H) := by
  have heq : pivotMatrix2026 = (fun u v => node2026 (pivotPermutation2026 u) v) := by apply Matrix.ext; unfold pivotMatrix2026 node2026 pivotPermutation2026; decide +kernel
  have hmoment : injectiveMoment H node2026 = injectiveMoment H pivotMatrix2026 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2026 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2026 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2026 (0 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2026 (0 : Fin 4) = raw4498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2026 raw4498; decide +kernel
    rw [heq]
    exact (canonical4498 hH).trans (sound576 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2026 (1 : Fin 4)) =
      Sparse.eval value582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2026 (1 : Fin 4) = raw3514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2026 raw3514; decide +kernel
    rw [heq]
    exact (canonical3514 hH).trans (sound582 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2026 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2026 (2 : Fin 4) = raw3444 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2026 raw3444; decide +kernel
    rw [heq]
    exact (canonical3444 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2026 (3 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2026 (3 : Fin 4) = raw3439 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2026 raw3439; decide +kernel
    rw [heq]
    exact (canonical3439 hH).trans (sound1180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2026 + (injectiveMoment H (mergeFirst pivotMatrix2026 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2026 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2026 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2026 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2026, value1180, value395, value576, value582, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2027 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2027 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem sound2027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2027 = Sparse.eval value2027 (momentVector H) := by
  have heq : pivotMatrix2027 = (fun u v => node2027 (pivotPermutation2027 u) v) := by apply Matrix.ext; unfold pivotMatrix2027 node2027 pivotPermutation2027; decide +kernel
  have hmoment : injectiveMoment H node2027 = injectiveMoment H pivotMatrix2027 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2027 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2027 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2027 (0 : Fin 4)) =
      Sparse.eval value579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2027 (0 : Fin 4) = raw4499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2027 raw4499; decide +kernel
    rw [heq]
    exact (canonical4499 hH).trans (sound579 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2027 (1 : Fin 4)) =
      Sparse.eval value581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2027 (1 : Fin 4) = raw3515 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2027 raw3515; decide +kernel
    rw [heq]
    exact (canonical3515 hH).trans (sound581 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2027 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2027 (2 : Fin 4) = raw3447 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2027 raw3447; decide +kernel
    rw [heq]
    exact (canonical3447 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2027 (3 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2027 (3 : Fin 4) = raw3445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2027 raw3445; decide +kernel
    rw [heq]
    exact (canonical3445 hH).trans (sound396 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2027 + (injectiveMoment H (mergeFirst pivotMatrix2027 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2027 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2027 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2027 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2027, value396, value579, value581, value775, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2028 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2028 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, -1, -1]]

theorem sound2028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2028 = Sparse.eval value2028 (momentVector H) := by
  have heq : pivotMatrix2028 = (fun u v => node2028 (pivotPermutation2028 u) v) := by apply Matrix.ext; unfold pivotMatrix2028 node2028 pivotPermutation2028; decide +kernel
  have hmoment : injectiveMoment H node2028 = injectiveMoment H pivotMatrix2028 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2028 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2028 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2028 (0 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (0 : Fin 4) = raw4745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw4745; decide +kernel
    rw [heq]
    exact (canonical4745 hH).trans (sound484 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2028 (1 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (1 : Fin 4) = raw3541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw3541; decide +kernel
    rw [heq]
    exact (canonical3541 hH).trans (sound488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2028 (2 : Fin 4)) =
      Sparse.eval value1120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (2 : Fin 4) = raw3450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw3450; decide +kernel
    rw [heq]
    exact (canonical3450 hH).trans (sound1120 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2028 (3 : Fin 4)) =
      Sparse.eval value411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (3 : Fin 4) = raw3446 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw3446; decide +kernel
    rw [heq]
    exact (canonical3446 hH).trans (sound411 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2028 + (injectiveMoment H (mergeFirst pivotMatrix2028 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2028 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2028 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2028 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2028, value1120, value411, value484, value488, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2029 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2029 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2]]

theorem sound2029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2029 = Sparse.eval value2029 (momentVector H) := by
  have heq : pivotMatrix2029 = (fun u v => node2029 (pivotPermutation2029 u) v) := by apply Matrix.ext; unfold pivotMatrix2029 node2029 pivotPermutation2029; decide +kernel
  have hmoment : injectiveMoment H node2029 = injectiveMoment H pivotMatrix2029 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2029 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2029 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2029 (0 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (0 : Fin 4) = raw7332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw7332; decide +kernel
    rw [heq]
    exact (canonical7332 hH).trans (sound832 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2029 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (1 : Fin 4) = raw3641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw3641; decide +kernel
    rw [heq]
    exact (canonical3641 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2029 (2 : Fin 4)) =
      Sparse.eval value411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (2 : Fin 4) = raw3451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw3451; decide +kernel
    rw [heq]
    exact (canonical3451 hH).trans (sound411 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2029 (3 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (3 : Fin 4) = raw3441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw3441; decide +kernel
    rw [heq]
    exact (canonical3441 hH).trans (sound406 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2029 + (injectiveMoment H (mergeFirst pivotMatrix2029 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2029 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2029 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2029 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2029, value406, value411, value496, value832, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2030 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2030 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem sound2030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2030 = Sparse.eval value2030 (momentVector H) := by
  have heq : pivotMatrix2030 = (fun u v => node2030 (pivotPermutation2030 u) v) := by apply Matrix.ext; unfold pivotMatrix2030 node2030 pivotPermutation2030; decide +kernel
  have hmoment : injectiveMoment H node2030 = injectiveMoment H pivotMatrix2030 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2030 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2030 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2030 (0 : Fin 4)) =
      Sparse.eval value595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2030 (0 : Fin 4) = raw3178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2030 raw3178; decide +kernel
    rw [heq]
    exact (canonical3178 hH).trans (sound595 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2030 (1 : Fin 4)) =
      Sparse.eval value582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2030 (1 : Fin 4) = raw3514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2030 raw3514; decide +kernel
    rw [heq]
    exact (canonical3514 hH).trans (sound582 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2030 (2 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2030 (2 : Fin 4) = raw3533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2030 raw3533; decide +kernel
    rw [heq]
    exact (canonical3533 hH).trans (sound474 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2030 (3 : Fin 4)) =
      Sparse.eval value451 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2030 (3 : Fin 4) = raw3537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2030 raw3537; decide +kernel
    rw [heq]
    exact (canonical3537 hH).trans (sound451 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2030 + (injectiveMoment H (mergeFirst pivotMatrix2030 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2030 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2030 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2030 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2030, value451, value474, value582, value595, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2031 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2031 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem sound2031 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2031 = Sparse.eval value2031 (momentVector H) := by
  have heq : pivotMatrix2031 = (fun u v => node2031 (pivotPermutation2031 u) v) := by apply Matrix.ext; unfold pivotMatrix2031 node2031 pivotPermutation2031; decide +kernel
  have hmoment : injectiveMoment H node2031 = injectiveMoment H pivotMatrix2031 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2031 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2031 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2031 (0 : Fin 4)) =
      Sparse.eval value596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2031 (0 : Fin 4) = raw3179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2031 raw3179; decide +kernel
    rw [heq]
    exact (canonical3179 hH).trans (sound596 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2031 (1 : Fin 4)) =
      Sparse.eval value581 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2031 (1 : Fin 4) = raw3515 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2031 raw3515; decide +kernel
    rw [heq]
    exact (canonical3515 hH).trans (sound581 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2031 (2 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2031 (2 : Fin 4) = raw3538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2031 raw3538; decide +kernel
    rw [heq]
    exact (canonical3538 hH).trans (sound450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2031 (3 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2031 (3 : Fin 4) = raw3539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2031 raw3539; decide +kernel
    rw [heq]
    exact (canonical3539 hH).trans (sound473 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2031 + (injectiveMoment H (mergeFirst pivotMatrix2031 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2031 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2031 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2031 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2031, value450, value473, value581, value596, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2032 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2032 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

theorem sound2032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2032 = Sparse.eval value2032 (momentVector H) := by
  have heq : pivotMatrix2032 = (fun u v => node2032 (pivotPermutation2032 u) v) := by apply Matrix.ext; unfold pivotMatrix2032 node2032 pivotPermutation2032; decide +kernel
  have hmoment : injectiveMoment H node2032 = injectiveMoment H pivotMatrix2032 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2032 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2032 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2032 (0 : Fin 4)) =
      Sparse.eval value956 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2032 (0 : Fin 4) = raw3194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2032 raw3194; decide +kernel
    rw [heq]
    exact (canonical3194 hH).trans (sound956 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2032 (1 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2032 (1 : Fin 4) = raw3525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2032 raw3525; decide +kernel
    rw [heq]
    exact (canonical3525 hH).trans (sound791 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2032 (2 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2032 (2 : Fin 4) = raw3558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2032 raw3558; decide +kernel
    rw [heq]
    exact (canonical3558 hH).trans (sound791 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2032 (3 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2032 (3 : Fin 4) = raw3567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2032 raw3567; decide +kernel
    rw [heq]
    exact (canonical3567 hH).trans (sound1027 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2032 + (injectiveMoment H (mergeFirst pivotMatrix2032 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2032 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2032 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2032 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2032, value1027, value791, value956, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2033 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2033 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

theorem sound2033 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2033 = Sparse.eval value2033 (momentVector H) := by
  have heq : pivotMatrix2033 = (fun u v => node2033 (pivotPermutation2033 u) v) := by apply Matrix.ext; unfold pivotMatrix2033 node2033 pivotPermutation2033; decide +kernel
  have hmoment : injectiveMoment H node2033 = injectiveMoment H pivotMatrix2033 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2033 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2033 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2033 (0 : Fin 4)) =
      Sparse.eval value929 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2033 (0 : Fin 4) = raw3212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2033 raw3212; decide +kernel
    rw [heq]
    exact (canonical3212 hH).trans (sound929 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2033 (1 : Fin 4)) =
      Sparse.eval value451 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2033 (1 : Fin 4) = raw3537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2033 raw3537; decide +kernel
    rw [heq]
    exact (canonical3537 hH).trans (sound451 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2033 (2 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2033 (2 : Fin 4) = raw3577 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2033 raw3577; decide +kernel
    rw [heq]
    exact (canonical3577 hH).trans (sound1235 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2033 (3 : Fin 4)) =
      Sparse.eval value1192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2033 (3 : Fin 4) = raw3582 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2033 raw3582; decide +kernel
    rw [heq]
    exact (canonical3582 hH).trans (sound1192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2033 + (injectiveMoment H (mergeFirst pivotMatrix2033 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2033 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2033 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2033 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2033, value1192, value1235, value451, value929, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2034 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2034 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem sound2034 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2034 = Sparse.eval value2034 (momentVector H) := by
  have heq : pivotMatrix2034 = (fun u v => node2034 (pivotPermutation2034 u) v) := by apply Matrix.ext; unfold pivotMatrix2034 node2034 pivotPermutation2034; decide +kernel
  have hmoment : injectiveMoment H node2034 = injectiveMoment H pivotMatrix2034 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2034 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2034 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2034 (0 : Fin 4)) =
      Sparse.eval value1250 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2034 (0 : Fin 4) = raw3787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2034 raw3787; decide +kernel
    rw [heq]
    exact (canonical3787 hH).trans (sound1250 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2034 (1 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2034 (1 : Fin 4) = raw3529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2034 raw3529; decide +kernel
    rw [heq]
    exact (canonical3529 hH).trans (sound1059 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2034 (2 : Fin 4)) =
      Sparse.eval value610 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2034 (2 : Fin 4) = raw3512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2034 raw3512; decide +kernel
    rw [heq]
    exact (canonical3512 hH).trans (sound610 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2034 (3 : Fin 4)) =
      Sparse.eval value1271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2034 (3 : Fin 4) = raw3511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2034 raw3511; decide +kernel
    rw [heq]
    exact (canonical3511 hH).trans (sound1271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2034 + (injectiveMoment H (mergeFirst pivotMatrix2034 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2034 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2034 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2034 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2034, value1059, value1250, value1271, value610, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2035 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2035 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem sound2035 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2035 = Sparse.eval value2035 (momentVector H) := by
  have heq : pivotMatrix2035 = (fun u v => node2035 (pivotPermutation2035 u) v) := by apply Matrix.ext; unfold pivotMatrix2035 node2035 pivotPermutation2035; decide +kernel
  have hmoment : injectiveMoment H node2035 = injectiveMoment H pivotMatrix2035 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2035 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2035 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2035 (0 : Fin 4)) =
      Sparse.eval value828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2035 (0 : Fin 4) = raw3796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2035 raw3796; decide +kernel
    rw [heq]
    exact (canonical3796 hH).trans (sound828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2035 (1 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2035 (1 : Fin 4) = raw3567 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2035 raw3567; decide +kernel
    rw [heq]
    exact (canonical3567 hH).trans (sound1027 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2035 (2 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2035 (2 : Fin 4) = raw3529 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2035 raw3529; decide +kernel
    rw [heq]
    exact (canonical3529 hH).trans (sound1059 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2035 (3 : Fin 4)) =
      Sparse.eval value791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2035 (3 : Fin 4) = raw3525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2035 raw3525; decide +kernel
    rw [heq]
    exact (canonical3525 hH).trans (sound791 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2035 + (injectiveMoment H (mergeFirst pivotMatrix2035 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2035 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2035 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2035 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2035, value1027, value1059, value791, value828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2036 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2036 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem sound2036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2036 = Sparse.eval value2036 (momentVector H) := by
  have heq : pivotMatrix2036 = (fun u v => node2036 (pivotPermutation2036 u) v) := by apply Matrix.ext; unfold pivotMatrix2036 node2036 pivotPermutation2036; decide +kernel
  have hmoment : injectiveMoment H node2036 = injectiveMoment H pivotMatrix2036 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2036 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2036 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2036 (0 : Fin 4)) =
      Sparse.eval value683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (0 : Fin 4) = raw4576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw4576; decide +kernel
    rw [heq]
    exact (canonical4576 hH).trans (sound683 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2036 (1 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (1 : Fin 4) = raw3596 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw3596; decide +kernel
    rw [heq]
    exact (canonical3596 hH).trans (sound520 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2036 (2 : Fin 4)) =
      Sparse.eval value591 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (2 : Fin 4) = raw3504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw3504; decide +kernel
    rw [heq]
    exact (canonical3504 hH).trans (sound591 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2036 (3 : Fin 4)) =
      Sparse.eval value1314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2036 (3 : Fin 4) = raw3498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2036 raw3498; decide +kernel
    rw [heq]
    exact (canonical3498 hH).trans (sound1314 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2036 + (injectiveMoment H (mergeFirst pivotMatrix2036 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2036 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2036 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2036 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2036, value1314, value520, value591, value683, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2037 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2037 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound2037 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2037 = Sparse.eval value2037 (momentVector H) := by
  have heq : pivotMatrix2037 = (fun u v => node2037 (pivotPermutation2037 u) v) := by apply Matrix.ext; unfold pivotMatrix2037 node2037 pivotPermutation2037; decide +kernel
  have hmoment : injectiveMoment H node2037 = injectiveMoment H pivotMatrix2037 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2037 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2037 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2037 (0 : Fin 4)) =
      Sparse.eval value1369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (0 : Fin 4) = raw4832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw4832; decide +kernel
    rw [heq]
    exact (canonical4832 hH).trans (sound1369 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2037 (1 : Fin 4)) =
      Sparse.eval value1376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (1 : Fin 4) = raw3614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw3614; decide +kernel
    rw [heq]
    exact (canonical3614 hH).trans (sound1376 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2037 (2 : Fin 4)) =
      Sparse.eval value1320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (2 : Fin 4) = raw3519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw3519; decide +kernel
    rw [heq]
    exact (canonical3519 hH).trans (sound1320 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2037 (3 : Fin 4)) =
      Sparse.eval value611 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (3 : Fin 4) = raw3516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw3516; decide +kernel
    rw [heq]
    exact (canonical3516 hH).trans (sound611 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2037 + (injectiveMoment H (mergeFirst pivotMatrix2037 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2037 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2037 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2037 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2037, value1320, value1369, value1376, value611, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2038 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2038 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem sound2038 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2038 = Sparse.eval value2038 (momentVector H) := by
  have heq : pivotMatrix2038 = (fun u v => node2038 (pivotPermutation2038 u) v) := by apply Matrix.ext; unfold pivotMatrix2038 node2038 pivotPermutation2038; decide +kernel
  have hmoment : injectiveMoment H node2038 = injectiveMoment H pivotMatrix2038 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2038 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2038 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2038 (0 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2038 (0 : Fin 4) = raw6524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2038 raw6524; decide +kernel
    rw [heq]
    exact (canonical6524 hH).trans (sound1075 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2038 (1 : Fin 4)) =
      Sparse.eval value1175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2038 (1 : Fin 4) = raw3639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2038 raw3639; decide +kernel
    rw [heq]
    exact (canonical3639 hH).trans (sound1175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2038 (2 : Fin 4)) =
      Sparse.eval value1300 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2038 (2 : Fin 4) = raw3520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2038 raw3520; decide +kernel
    rw [heq]
    exact (canonical3520 hH).trans (sound1300 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2038 (3 : Fin 4)) =
      Sparse.eval value582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2038 (3 : Fin 4) = raw3514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2038 raw3514; decide +kernel
    rw [heq]
    exact (canonical3514 hH).trans (sound582 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2038 + (injectiveMoment H (mergeFirst pivotMatrix2038 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2038 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2038 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2038 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2038, value1075, value1175, value1300, value582, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2039 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2039 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem sound2039 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2039 = Sparse.eval value2039 (momentVector H) := by
  have heq : pivotMatrix2039 = (fun u v => node2039 (pivotPermutation2039 u) v) := by apply Matrix.ext; unfold pivotMatrix2039 node2039 pivotPermutation2039; decide +kernel
  have hmoment : injectiveMoment H node2039 = injectiveMoment H pivotMatrix2039 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2039 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2039 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2039 (0 : Fin 4)) =
      Sparse.eval value596 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2039 (0 : Fin 4) = raw4607 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2039 raw4607; decide +kernel
    rw [heq]
    exact (canonical4607 hH).trans (sound596 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2039 (1 : Fin 4)) =
      Sparse.eval value461 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2039 (1 : Fin 4) = raw3611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2039 raw3611; decide +kernel
    rw [heq]
    exact (canonical3611 hH).trans (sound461 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2039 (2 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2039 (2 : Fin 4) = raw3542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2039 raw3542; decide +kernel
    rw [heq]
    exact (canonical3542 hH).trans (sound1306 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2039 (3 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2039 (3 : Fin 4) = raw3538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2039 raw3538; decide +kernel
    rw [heq]
    exact (canonical3538 hH).trans (sound450 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2039 + (injectiveMoment H (mergeFirst pivotMatrix2039 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2039 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2039 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2039 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2039, value1306, value450, value461, value596, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2040 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2040 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem sound2040 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2040 = Sparse.eval value2040 (momentVector H) := by
  have heq : pivotMatrix2040 = (fun u v => node2040 (pivotPermutation2040 u) v) := by apply Matrix.ext; unfold pivotMatrix2040 node2040 pivotPermutation2040; decide +kernel
  have hmoment : injectiveMoment H node2040 = injectiveMoment H pivotMatrix2040 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2040 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2040 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2040 (0 : Fin 4)) =
      Sparse.eval value684 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2040 (0 : Fin 4) = raw4608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2040 raw4608; decide +kernel
    rw [heq]
    exact (canonical4608 hH).trans (sound684 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2040 (1 : Fin 4)) =
      Sparse.eval value588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2040 (1 : Fin 4) = raw3613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2040 raw3613; decide +kernel
    rw [heq]
    exact (canonical3613 hH).trans (sound588 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2040 (2 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2040 (2 : Fin 4) = raw3544 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2040 raw3544; decide +kernel
    rw [heq]
    exact (canonical3544 hH).trans (sound1309 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2040 (3 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2040 (3 : Fin 4) = raw3540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2040 raw3540; decide +kernel
    rw [heq]
    exact (canonical3540 hH).trans (sound521 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2040 + (injectiveMoment H (mergeFirst pivotMatrix2040 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2040 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2040 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2040 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2040, value1309, value521, value588, value684, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2041 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2041 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem sound2041 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2041 = Sparse.eval value2041 (momentVector H) := by
  have heq : pivotMatrix2041 = (fun u v => node2041 (pivotPermutation2041 u) v) := by apply Matrix.ext; unfold pivotMatrix2041 node2041 pivotPermutation2041; decide +kernel
  have hmoment : injectiveMoment H node2041 = injectiveMoment H pivotMatrix2041 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2041 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2041 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2041 (0 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2041 (0 : Fin 4) = raw4609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2041 raw4609; decide +kernel
    rw [heq]
    exact (canonical4609 hH).trans (sound1310 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2041 (1 : Fin 4)) =
      Sparse.eval value1376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2041 (1 : Fin 4) = raw3614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2041 raw3614; decide +kernel
    rw [heq]
    exact (canonical3614 hH).trans (sound1376 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2041 (2 : Fin 4)) =
      Sparse.eval value1311 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2041 (2 : Fin 4) = raw3545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2041 raw3545; decide +kernel
    rw [heq]
    exact (canonical3545 hH).trans (sound1311 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2041 (3 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2041 (3 : Fin 4) = raw3541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2041 raw3541; decide +kernel
    rw [heq]
    exact (canonical3541 hH).trans (sound488 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2041 + (injectiveMoment H (mergeFirst pivotMatrix2041 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2041 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2041 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2041 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2041, value1310, value1311, value1376, value488, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2042 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2042 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound2042 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2042 = Sparse.eval value2042 (momentVector H) := by
  have heq : pivotMatrix2042 = (fun u v => node2042 (pivotPermutation2042 u) v) := by apply Matrix.ext; unfold pivotMatrix2042 node2042 pivotPermutation2042; decide +kernel
  have hmoment : injectiveMoment H node2042 = injectiveMoment H pivotMatrix2042 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2042 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2042 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2042 (0 : Fin 4)) =
      Sparse.eval value1308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2042 (0 : Fin 4) = raw4610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2042 raw4610; decide +kernel
    rw [heq]
    exact (canonical4610 hH).trans (sound1308 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2042 (1 : Fin 4)) =
      Sparse.eval value1313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2042 (1 : Fin 4) = raw3615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2042 raw3615; decide +kernel
    rw [heq]
    exact (canonical3615 hH).trans (sound1313 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2042 (2 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2042 (2 : Fin 4) = raw3547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2042 raw3547; decide +kernel
    rw [heq]
    exact (canonical3547 hH).trans (sound819 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2042 (3 : Fin 4)) =
      Sparse.eval value1301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2042 (3 : Fin 4) = raw3543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2042 raw3543; decide +kernel
    rw [heq]
    exact (canonical3543 hH).trans (sound1301 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2042 + (injectiveMoment H (mergeFirst pivotMatrix2042 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2042 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2042 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2042 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2042, value1301, value1308, value1313, value819, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2043 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2043 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem sound2043 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2043 = Sparse.eval value2043 (momentVector H) := by
  have heq : pivotMatrix2043 = (fun u v => node2043 (pivotPermutation2043 u) v) := by apply Matrix.ext; unfold pivotMatrix2043 node2043 pivotPermutation2043; decide +kernel
  have hmoment : injectiveMoment H node2043 = injectiveMoment H pivotMatrix2043 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2043 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2043 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2043 (0 : Fin 4)) =
      Sparse.eval value820 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2043 (0 : Fin 4) = raw4836 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2043 raw4836; decide +kernel
    rw [heq]
    exact (canonical4836 hH).trans (sound820 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2043 (1 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2043 (1 : Fin 4) = raw3618 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2043 raw3618; decide +kernel
    rw [heq]
    exact (canonical3618 hH).trans (sound808 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2043 (2 : Fin 4)) =
      Sparse.eval value819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2043 (2 : Fin 4) = raw3546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2043 raw3546; decide +kernel
    rw [heq]
    exact (canonical3546 hH).trans (sound819 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2043 (3 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2043 (3 : Fin 4) = raw3541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2043 raw3541; decide +kernel
    rw [heq]
    exact (canonical3541 hH).trans (sound488 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2043 + (injectiveMoment H (mergeFirst pivotMatrix2043 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2043 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2043 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2043 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2043, value488, value808, value819, value820, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2044 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2044 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

theorem sound2044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2044 = Sparse.eval value2044 (momentVector H) := by
  have heq : pivotMatrix2044 = (fun u v => node2044 (pivotPermutation2044 u) v) := by apply Matrix.ext; unfold pivotMatrix2044 node2044 pivotPermutation2044; decide +kernel
  have hmoment : injectiveMoment H node2044 = injectiveMoment H pivotMatrix2044 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2044 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2044 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2044 (0 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2044 (0 : Fin 4) = raw7227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2044 raw7227; decide +kernel
    rw [heq]
    exact (canonical7227 hH).trans (sound1276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2044 (1 : Fin 4)) =
      Sparse.eval value612 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2044 (1 : Fin 4) = raw3642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2044 raw3642; decide +kernel
    rw [heq]
    exact (canonical3642 hH).trans (sound612 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2044 (2 : Fin 4)) =
      Sparse.eval value521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2044 (2 : Fin 4) = raw3549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2044 raw3549; decide +kernel
    rw [heq]
    exact (canonical3549 hH).trans (sound521 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2044 (3 : Fin 4)) =
      Sparse.eval value520 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2044 (3 : Fin 4) = raw3531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2044 raw3531; decide +kernel
    rw [heq]
    exact (canonical3531 hH).trans (sound520 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2044 + (injectiveMoment H (mergeFirst pivotMatrix2044 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2044 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2044 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2044 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2044, value1276, value520, value521, value612, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2045 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2045 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem sound2045 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2045 = Sparse.eval value2045 (momentVector H) := by
  have heq : pivotMatrix2045 = (fun u v => node2045 (pivotPermutation2045 u) v) := by apply Matrix.ext; unfold pivotMatrix2045 node2045 pivotPermutation2045; decide +kernel
  have hmoment : injectiveMoment H node2045 = injectiveMoment H pivotMatrix2045 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2045 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2045 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2045 (0 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2045 (0 : Fin 4) = raw7229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2045 raw7229; decide +kernel
    rw [heq]
    exact (canonical7229 hH).trans (sound1278 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2045 (1 : Fin 4)) =
      Sparse.eval value462 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2045 (1 : Fin 4) = raw3643 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2045 raw3643; decide +kernel
    rw [heq]
    exact (canonical3643 hH).trans (sound462 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2045 (2 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2045 (2 : Fin 4) = raw3550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2045 raw3550; decide +kernel
    rw [heq]
    exact (canonical3550 hH).trans (sound450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2045 (3 : Fin 4)) =
      Sparse.eval value451 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2045 (3 : Fin 4) = raw3537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2045 raw3537; decide +kernel
    rw [heq]
    exact (canonical3537 hH).trans (sound451 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2045 + (injectiveMoment H (mergeFirst pivotMatrix2045 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2045 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2045 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2045 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2045, value1278, value450, value451, value462, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2046 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2046 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem sound2046 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2046 = Sparse.eval value2046 (momentVector H) := by
  have heq : pivotMatrix2046 = (fun u v => node2046 (pivotPermutation2046 u) v) := by apply Matrix.ext; unfold pivotMatrix2046 node2046 pivotPermutation2046; decide +kernel
  have hmoment : injectiveMoment H node2046 = injectiveMoment H pivotMatrix2046 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2046 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2046 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2046 (0 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2046 (0 : Fin 4) = raw6531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2046 raw6531; decide +kernel
    rw [heq]
    exact (canonical6531 hH).trans (sound1080 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2046 (1 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2046 (1 : Fin 4) = raw3640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2046 raw3640; decide +kernel
    rw [heq]
    exact (canonical3640 hH).trans (sound1173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2046 (2 : Fin 4)) =
      Sparse.eval value1306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2046 (2 : Fin 4) = raw3548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2046 raw3548; decide +kernel
    rw [heq]
    exact (canonical3548 hH).trans (sound1306 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2046 (3 : Fin 4)) =
      Sparse.eval value451 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2046 (3 : Fin 4) = raw3537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2046 raw3537; decide +kernel
    rw [heq]
    exact (canonical3537 hH).trans (sound451 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2046 + (injectiveMoment H (mergeFirst pivotMatrix2046 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2046 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2046 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2046 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2046, value1080, value1173, value1306, value451, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2047 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2047 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

theorem sound2047 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2047 = Sparse.eval value2047 (momentVector H) := by
  have heq : pivotMatrix2047 = (fun u v => node2047 (pivotPermutation2047 u) v) := by apply Matrix.ext; unfold pivotMatrix2047 node2047 pivotPermutation2047; decide +kernel
  have hmoment : injectiveMoment H node2047 = injectiveMoment H pivotMatrix2047 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2047 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2047 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2047 (0 : Fin 4)) =
      Sparse.eval value927 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2047 (0 : Fin 4) = raw4613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2047 raw4613; decide +kernel
    rw [heq]
    exact (canonical4613 hH).trans (sound927 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2047 (1 : Fin 4)) =
      Sparse.eval value577 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2047 (1 : Fin 4) = raw3617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2047 raw3617; decide +kernel
    rw [heq]
    exact (canonical3617 hH).trans (sound577 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2047 (2 : Fin 4)) =
      Sparse.eval value1189 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2047 (2 : Fin 4) = raw3586 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2047 raw3586; decide +kernel
    rw [heq]
    exact (canonical3586 hH).trans (sound1189 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2047 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2047 (3 : Fin 4) = raw3583 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2047 raw3583; decide +kernel
    rw [heq]
    exact (canonical3583 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2047 + (injectiveMoment H (mergeFirst pivotMatrix2047 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2047 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2047 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2047 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2047, value1189, value1234, value577, value927, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
