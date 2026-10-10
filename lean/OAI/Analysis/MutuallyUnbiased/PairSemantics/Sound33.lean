import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical124
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical125
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical132
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical134
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical135
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical136
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2112 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2112 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem sound2112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2112 = Sparse.eval value2112 (momentVector H) := by
  have heq : pivotMatrix2112 = (fun u v => node2112 (pivotPermutation2112 u) v) := by apply Matrix.ext; unfold pivotMatrix2112 node2112 pivotPermutation2112; decide +kernel
  have hmoment : injectiveMoment H node2112 = injectiveMoment H pivotMatrix2112 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2112 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2112 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2112 (0 : Fin 5)) =
      Sparse.eval value542 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2112 (0 : Fin 5) = raw2710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2112 raw2710; decide +kernel
    rw [heq]
    exact (canonical2710 hH).trans (sound542 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2112 (1 : Fin 5)) =
      Sparse.eval value631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2112 (1 : Fin 5) = raw3998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2112 raw3998; decide +kernel
    rw [heq]
    exact (canonical3998 hH).trans (sound631 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2112 (2 : Fin 5)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2112 (2 : Fin 5) = raw4020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2112 raw4020; decide +kernel
    rw [heq]
    exact (canonical4020 hH).trans (sound197 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2112 (3 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2112 (3 : Fin 5) = raw4023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2112 raw4023; decide +kernel
    rw [heq]
    exact (canonical4023 hH).trans (sound641 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2112 (4 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2112 (4 : Fin 5) = raw4024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2112 raw4024; decide +kernel
    rw [heq]
    exact (canonical4024 hH).trans (sound642 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2112 + (injectiveMoment H (mergeFirst pivotMatrix2112 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2112 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2112 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2112 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2112 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2112, value197, value542, value631, value641, value642, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2113 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2113 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem sound2113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2113 = Sparse.eval value2113 (momentVector H) := by
  have heq : pivotMatrix2113 = (fun u v => node2113 (pivotPermutation2113 u) v) := by apply Matrix.ext; unfold pivotMatrix2113 node2113 pivotPermutation2113; decide +kernel
  have hmoment : injectiveMoment H node2113 = injectiveMoment H pivotMatrix2113 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2113 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2113 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2113 (0 : Fin 5)) =
      Sparse.eval value543 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2113 (0 : Fin 5) = raw2711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2113 raw2711; decide +kernel
    rw [heq]
    exact (canonical2711 hH).trans (sound543 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2113 (1 : Fin 5)) =
      Sparse.eval value632 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2113 (1 : Fin 5) = raw3999 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2113 raw3999; decide +kernel
    rw [heq]
    exact (canonical3999 hH).trans (sound632 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2113 (2 : Fin 5)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2113 (2 : Fin 5) = raw4021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2113 raw4021; decide +kernel
    rw [heq]
    exact (canonical4021 hH).trans (sound201 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2113 (3 : Fin 5)) =
      Sparse.eval value644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2113 (3 : Fin 5) = raw4025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2113 raw4025; decide +kernel
    rw [heq]
    exact (canonical4025 hH).trans (sound644 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2113 (4 : Fin 5)) =
      Sparse.eval value645 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2113 (4 : Fin 5) = raw4026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2113 raw4026; decide +kernel
    rw [heq]
    exact (canonical4026 hH).trans (sound645 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2113 + (injectiveMoment H (mergeFirst pivotMatrix2113 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2113 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2113 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2113 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2113 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2113, value201, value543, value632, value644, value645, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2114 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2114 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem sound2114 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2114 = Sparse.eval value2114 (momentVector H) := by
  have heq : pivotMatrix2114 = (fun u v => node2114 (pivotPermutation2114 u) v) := by apply Matrix.ext; unfold pivotMatrix2114 node2114 pivotPermutation2114; decide +kernel
  have hmoment : injectiveMoment H node2114 = injectiveMoment H pivotMatrix2114 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2114 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2114 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2114 (0 : Fin 5)) =
      Sparse.eval value544 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2114 (0 : Fin 5) = raw2712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2114 raw2712; decide +kernel
    rw [heq]
    exact (canonical2712 hH).trans (sound544 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2114 (1 : Fin 5)) =
      Sparse.eval value633 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2114 (1 : Fin 5) = raw4000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2114 raw4000; decide +kernel
    rw [heq]
    exact (canonical4000 hH).trans (sound633 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2114 (2 : Fin 5)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2114 (2 : Fin 5) = raw4022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2114 raw4022; decide +kernel
    rw [heq]
    exact (canonical4022 hH).trans (sound169 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2114 (3 : Fin 5)) =
      Sparse.eval value645 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2114 (3 : Fin 5) = raw4026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2114 raw4026; decide +kernel
    rw [heq]
    exact (canonical4026 hH).trans (sound645 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2114 (4 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2114 (4 : Fin 5) = raw4027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2114 raw4027; decide +kernel
    rw [heq]
    exact (canonical4027 hH).trans (sound646 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2114 + (injectiveMoment H (mergeFirst pivotMatrix2114 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2114 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2114 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2114 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2114 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2114, value169, value544, value633, value645, value646, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2115 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2115 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound2115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2115 = Sparse.eval value2115 (momentVector H) := by
  have heq : pivotMatrix2115 = (fun u v => node2115 (pivotPermutation2115 u) v) := by apply Matrix.ext; unfold pivotMatrix2115 node2115 pivotPermutation2115; decide +kernel
  have hmoment : injectiveMoment H node2115 = injectiveMoment H pivotMatrix2115 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2115 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2115 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2115 (0 : Fin 5)) =
      Sparse.eval value547 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2115 (0 : Fin 5) = raw2717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2115 raw2717; decide +kernel
    rw [heq]
    exact (canonical2717 hH).trans (sound547 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2115 (1 : Fin 5)) =
      Sparse.eval value635 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2115 (1 : Fin 5) = raw4003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2115 raw4003; decide +kernel
    rw [heq]
    exact (canonical4003 hH).trans (sound635 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2115 (2 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2115 (2 : Fin 5) = raw4027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2115 raw4027; decide +kernel
    rw [heq]
    exact (canonical4027 hH).trans (sound646 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2115 (3 : Fin 5)) =
      Sparse.eval value647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2115 (3 : Fin 5) = raw4032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2115 raw4032; decide +kernel
    rw [heq]
    exact (canonical4032 hH).trans (sound647 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2115 (4 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2115 (4 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2115 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2115 + (injectiveMoment H (mergeFirst pivotMatrix2115 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2115 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2115 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2115 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2115 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2115, value547, value635, value641, value646, value647, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2116 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2116 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound2116 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2116 = Sparse.eval value2116 (momentVector H) := by
  have heq : pivotMatrix2116 = (fun u v => node2116 (pivotPermutation2116 u) v) := by apply Matrix.ext; unfold pivotMatrix2116 node2116 pivotPermutation2116; decide +kernel
  have hmoment : injectiveMoment H node2116 = injectiveMoment H pivotMatrix2116 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2116 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2116 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2116 (0 : Fin 5)) =
      Sparse.eval value549 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2116 (0 : Fin 5) = raw2720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2116 raw2720; decide +kernel
    rw [heq]
    exact (canonical2720 hH).trans (sound549 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2116 (1 : Fin 5)) =
      Sparse.eval value636 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2116 (1 : Fin 5) = raw4006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2116 raw4006; decide +kernel
    rw [heq]
    exact (canonical4006 hH).trans (sound636 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2116 (2 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2116 (2 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2116 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2116 (3 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2116 (3 : Fin 5) = raw4035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2116 raw4035; decide +kernel
    rw [heq]
    exact (canonical4035 hH).trans (sound648 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2116 (4 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2116 (4 : Fin 5) = raw4036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2116 raw4036; decide +kernel
    rw [heq]
    exact (canonical4036 hH).trans (sound648 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2116 + (injectiveMoment H (mergeFirst pivotMatrix2116 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2116 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2116 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2116 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2116 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2116, value549, value636, value641, value648, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2117 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem sound2117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2117 = Sparse.eval value2117 (momentVector H) := by
  have heq : pivotMatrix2117 = (fun u v => node2117 (pivotPermutation2117 u) v) := by apply Matrix.ext; unfold pivotMatrix2117 node2117 pivotPermutation2117; decide +kernel
  have hmoment : injectiveMoment H node2117 = injectiveMoment H pivotMatrix2117 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2117 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2117 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2117 (0 : Fin 5)) =
      Sparse.eval value550 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2117 (0 : Fin 5) = raw2722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2117 raw2722; decide +kernel
    rw [heq]
    exact (canonical2722 hH).trans (sound550 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2117 (1 : Fin 5)) =
      Sparse.eval value637 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2117 (1 : Fin 5) = raw4008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2117 raw4008; decide +kernel
    rw [heq]
    exact (canonical4008 hH).trans (sound637 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2117 (2 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2117 (2 : Fin 5) = raw4035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2117 raw4035; decide +kernel
    rw [heq]
    exact (canonical4035 hH).trans (sound648 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2117 (3 : Fin 5)) =
      Sparse.eval value649 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2117 (3 : Fin 5) = raw4038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2117 raw4038; decide +kernel
    rw [heq]
    exact (canonical4038 hH).trans (sound649 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2117 (4 : Fin 5)) =
      Sparse.eval value650 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2117 (4 : Fin 5) = raw4039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2117 raw4039; decide +kernel
    rw [heq]
    exact (canonical4039 hH).trans (sound650 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2117 + (injectiveMoment H (mergeFirst pivotMatrix2117 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2117 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2117 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2117 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2117 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2117, value550, value637, value648, value649, value650, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2118 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2118 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem sound2118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2118 = Sparse.eval value2118 (momentVector H) := by
  have heq : pivotMatrix2118 = (fun u v => node2118 (pivotPermutation2118 u) v) := by apply Matrix.ext; unfold pivotMatrix2118 node2118 pivotPermutation2118; decide +kernel
  have hmoment : injectiveMoment H node2118 = injectiveMoment H pivotMatrix2118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2118 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2118 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2118 (0 : Fin 5)) =
      Sparse.eval value704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (0 : Fin 5) = raw4912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4912; decide +kernel
    rw [heq]
    exact (canonical4912 hH).trans (sound704 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2118 (1 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (1 : Fin 5) = raw4067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4067; decide +kernel
    rw [heq]
    exact (canonical4067 hH).trans (sound655 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2118 (2 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (2 : Fin 5) = raw4031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4031; decide +kernel
    rw [heq]
    exact (canonical4031 hH).trans (sound642 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2118 (3 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (3 : Fin 5) = raw4024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4024; decide +kernel
    rw [heq]
    exact (canonical4024 hH).trans (sound642 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2118 (4 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2118 (4 : Fin 5) = raw4023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2118 raw4023; decide +kernel
    rw [heq]
    exact (canonical4023 hH).trans (sound641 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2118 + (injectiveMoment H (mergeFirst pivotMatrix2118 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2118 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2118, value641, value642, value655, value704, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2119 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2119 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2119 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2119 = Sparse.eval value2119 (momentVector H) := by
  have heq : pivotMatrix2119 = (fun u v => node2119 (pivotPermutation2119 u) v) := by apply Matrix.ext; unfold pivotMatrix2119 node2119 pivotPermutation2119; decide +kernel
  have hmoment : injectiveMoment H node2119 = injectiveMoment H pivotMatrix2119 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2119 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2119 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2119 (0 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2119 (0 : Fin 5) = raw4913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2119 raw4913; decide +kernel
    rw [heq]
    exact (canonical4913 hH).trans (sound705 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2119 (1 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2119 (1 : Fin 5) = raw4071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2119 raw4071; decide +kernel
    rw [heq]
    exact (canonical4071 hH).trans (sound659 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2119 (2 : Fin 5)) =
      Sparse.eval value647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2119 (2 : Fin 5) = raw4032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2119 raw4032; decide +kernel
    rw [heq]
    exact (canonical4032 hH).trans (sound647 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2119 (3 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2119 (3 : Fin 5) = raw4027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2119 raw4027; decide +kernel
    rw [heq]
    exact (canonical4027 hH).trans (sound646 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2119 (4 : Fin 5)) =
      Sparse.eval value645 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2119 (4 : Fin 5) = raw4026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2119 raw4026; decide +kernel
    rw [heq]
    exact (canonical4026 hH).trans (sound645 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2119 + (injectiveMoment H (mergeFirst pivotMatrix2119 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2119 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2119 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2119 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2119 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2119, value645, value646, value647, value659, value705, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2120 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2120 = Sparse.eval value2120 (momentVector H) := by
  have heq : pivotMatrix2120 = (fun u v => node2120 (pivotPermutation2120 u) v) := by apply Matrix.ext; unfold pivotMatrix2120 node2120 pivotPermutation2120; decide +kernel
  have hmoment : injectiveMoment H node2120 = injectiveMoment H pivotMatrix2120 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2120 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2120 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2120 (0 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2120 (0 : Fin 5) = raw4914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2120 raw4914; decide +kernel
    rw [heq]
    exact (canonical4914 hH).trans (sound667 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2120 (1 : Fin 5)) =
      Sparse.eval value1291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2120 (1 : Fin 5) = raw4072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2120 raw4072; decide +kernel
    rw [heq]
    exact (canonical4072 hH).trans (sound1291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2120 (2 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2120 (2 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2120 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2120 (3 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2120 (3 : Fin 5) = raw4028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2120 raw4028; decide +kernel
    rw [heq]
    exact (canonical4028 hH).trans (sound646 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2120 (4 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2120 (4 : Fin 5) = raw4027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2120 raw4027; decide +kernel
    rw [heq]
    exact (canonical4027 hH).trans (sound646 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2120 + (injectiveMoment H (mergeFirst pivotMatrix2120 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2120 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2120 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2120 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2120 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2120, value1291, value641, value646, value667, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2121 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem sound2121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2121 = Sparse.eval value2121 (momentVector H) := by
  have heq : pivotMatrix2121 = (fun u v => node2121 (pivotPermutation2121 u) v) := by apply Matrix.ext; unfold pivotMatrix2121 node2121 pivotPermutation2121; decide +kernel
  have hmoment : injectiveMoment H node2121 = injectiveMoment H pivotMatrix2121 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2121 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2121 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2121 (0 : Fin 5)) =
      Sparse.eval value706 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2121 (0 : Fin 5) = raw4916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2121 raw4916; decide +kernel
    rw [heq]
    exact (canonical4916 hH).trans (sound706 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2121 (1 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2121 (1 : Fin 5) = raw4077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2121 raw4077; decide +kernel
    rw [heq]
    exact (canonical4077 hH).trans (sound661 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2121 (2 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2121 (2 : Fin 5) = raw4035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2121 raw4035; decide +kernel
    rw [heq]
    exact (canonical4035 hH).trans (sound648 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2121 (3 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2121 (3 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2121 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2121 (4 : Fin 5)) =
      Sparse.eval value647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2121 (4 : Fin 5) = raw4032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2121 raw4032; decide +kernel
    rw [heq]
    exact (canonical4032 hH).trans (sound647 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2121 + (injectiveMoment H (mergeFirst pivotMatrix2121 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2121 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2121 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2121 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2121 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2121, value641, value647, value648, value661, value706, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2122 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem sound2122 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2122 = Sparse.eval value2122 (momentVector H) := by
  have heq : pivotMatrix2122 = (fun u v => node2122 (pivotPermutation2122 u) v) := by apply Matrix.ext; unfold pivotMatrix2122 node2122 pivotPermutation2122; decide +kernel
  have hmoment : injectiveMoment H node2122 = injectiveMoment H pivotMatrix2122 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2122 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2122 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2122 (0 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2122 (0 : Fin 5) = raw4919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2122 raw4919; decide +kernel
    rw [heq]
    exact (canonical4919 hH).trans (sound699 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2122 (1 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2122 (1 : Fin 5) = raw4081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2122 raw4081; decide +kernel
    rw [heq]
    exact (canonical4081 hH).trans (sound663 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2122 (2 : Fin 5)) =
      Sparse.eval value650 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2122 (2 : Fin 5) = raw4039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2122 raw4039; decide +kernel
    rw [heq]
    exact (canonical4039 hH).trans (sound650 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2122 (3 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2122 (3 : Fin 5) = raw4036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2122 raw4036; decide +kernel
    rw [heq]
    exact (canonical4036 hH).trans (sound648 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2122 (4 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2122 (4 : Fin 5) = raw4035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2122 raw4035; decide +kernel
    rw [heq]
    exact (canonical4035 hH).trans (sound648 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2122 + (injectiveMoment H (mergeFirst pivotMatrix2122 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2122 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2122 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2122 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2122 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2122, value648, value650, value663, value699, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2123 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2123 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem sound2123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2123 = Sparse.eval value2123 (momentVector H) := by
  have heq : pivotMatrix2123 = (fun u v => node2123 (pivotPermutation2123 u) v) := by apply Matrix.ext; unfold pivotMatrix2123 node2123 pivotPermutation2123; decide +kernel
  have hmoment : injectiveMoment H node2123 = injectiveMoment H pivotMatrix2123 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2123 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2123 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2123 (0 : Fin 5)) =
      Sparse.eval value552 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2123 (0 : Fin 5) = raw2736 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2123 raw2736; decide +kernel
    rw [heq]
    exact (canonical2736 hH).trans (sound552 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2123 (1 : Fin 5)) =
      Sparse.eval value638 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2123 (1 : Fin 5) = raw4018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2123 raw4018; decide +kernel
    rw [heq]
    exact (canonical4018 hH).trans (sound638 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2123 (2 : Fin 5)) =
      Sparse.eval value638 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2123 (2 : Fin 5) = raw4051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2123 raw4051; decide +kernel
    rw [heq]
    exact (canonical4051 hH).trans (sound638 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2123 (3 : Fin 5)) =
      Sparse.eval value652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2123 (3 : Fin 5) = raw4055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2123 raw4055; decide +kernel
    rw [heq]
    exact (canonical4055 hH).trans (sound652 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2123 (4 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2123 (4 : Fin 5) = raw4058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2123 raw4058; decide +kernel
    rw [heq]
    exact (canonical4058 hH).trans (sound653 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2123 + (injectiveMoment H (mergeFirst pivotMatrix2123 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2123 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2123 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2123 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2123 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2123, value552, value638, value652, value653, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2124 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2124 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem sound2124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2124 = Sparse.eval value2124 (momentVector H) := by
  have heq : pivotMatrix2124 = (fun u v => node2124 (pivotPermutation2124 u) v) := by apply Matrix.ext; unfold pivotMatrix2124 node2124 pivotPermutation2124; decide +kernel
  have hmoment : injectiveMoment H node2124 = injectiveMoment H pivotMatrix2124 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2124 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2124 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2124 (0 : Fin 5)) =
      Sparse.eval value553 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2124 (0 : Fin 5) = raw2737 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2124 raw2737; decide +kernel
    rw [heq]
    exact (canonical2737 hH).trans (sound553 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2124 (1 : Fin 5)) =
      Sparse.eval value639 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2124 (1 : Fin 5) = raw4019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2124 raw4019; decide +kernel
    rw [heq]
    exact (canonical4019 hH).trans (sound639 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2124 (2 : Fin 5)) =
      Sparse.eval value639 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2124 (2 : Fin 5) = raw4052 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2124 raw4052; decide +kernel
    rw [heq]
    exact (canonical4052 hH).trans (sound639 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2124 (3 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2124 (3 : Fin 5) = raw4058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2124 raw4058; decide +kernel
    rw [heq]
    exact (canonical4058 hH).trans (sound653 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2124 (4 : Fin 5)) =
      Sparse.eval value562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2124 (4 : Fin 5) = raw4059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2124 raw4059; decide +kernel
    rw [heq]
    exact (canonical4059 hH).trans (sound562 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2124 + (injectiveMoment H (mergeFirst pivotMatrix2124 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2124 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2124 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2124 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2124 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2124, value553, value562, value639, value653, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2125 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem sound2125 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2125 = Sparse.eval value2125 (momentVector H) := by
  have heq : pivotMatrix2125 = (fun u v => node2125 (pivotPermutation2125 u) v) := by apply Matrix.ext; unfold pivotMatrix2125 node2125 pivotPermutation2125; decide +kernel
  have hmoment : injectiveMoment H node2125 = injectiveMoment H pivotMatrix2125 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2125 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2125 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2125 (0 : Fin 5)) =
      Sparse.eval value555 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2125 (0 : Fin 5) = raw2744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2125 raw2744; decide +kernel
    rw [heq]
    exact (canonical2744 hH).trans (sound555 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2125 (1 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2125 (1 : Fin 5) = raw4023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2125 raw4023; decide +kernel
    rw [heq]
    exact (canonical4023 hH).trans (sound641 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2125 (2 : Fin 5)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2125 (2 : Fin 5) = raw4060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2125 raw4060; decide +kernel
    rw [heq]
    exact (canonical4060 hH).trans (sound291 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2125 (3 : Fin 5)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2125 (3 : Fin 5) = raw4065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2125 raw4065; decide +kernel
    rw [heq]
    exact (canonical4065 hH).trans (sound291 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2125 (4 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2125 (4 : Fin 5) = raw4067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2125 raw4067; decide +kernel
    rw [heq]
    exact (canonical4067 hH).trans (sound655 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2125 + (injectiveMoment H (mergeFirst pivotMatrix2125 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2125 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2125 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2125 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2125 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2125, value291, value555, value641, value655, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2126 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem sound2126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2126 = Sparse.eval value2126 (momentVector H) := by
  have heq : pivotMatrix2126 = (fun u v => node2126 (pivotPermutation2126 u) v) := by apply Matrix.ext; unfold pivotMatrix2126 node2126 pivotPermutation2126; decide +kernel
  have hmoment : injectiveMoment H node2126 = injectiveMoment H pivotMatrix2126 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2126 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2126 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2126 (0 : Fin 5)) =
      Sparse.eval value556 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2126 (0 : Fin 5) = raw2745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2126 raw2745; decide +kernel
    rw [heq]
    exact (canonical2745 hH).trans (sound556 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2126 (1 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2126 (1 : Fin 5) = raw4024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2126 raw4024; decide +kernel
    rw [heq]
    exact (canonical4024 hH).trans (sound642 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2126 (2 : Fin 5)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2126 (2 : Fin 5) = raw4061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2126 raw4061; decide +kernel
    rw [heq]
    exact (canonical4061 hH).trans (sound203 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2126 (3 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2126 (3 : Fin 5) = raw4067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2126 raw4067; decide +kernel
    rw [heq]
    exact (canonical4067 hH).trans (sound655 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2126 (4 : Fin 5)) =
      Sparse.eval value656 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2126 (4 : Fin 5) = raw4068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2126 raw4068; decide +kernel
    rw [heq]
    exact (canonical4068 hH).trans (sound656 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2126 + (injectiveMoment H (mergeFirst pivotMatrix2126 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2126 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2126 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2126 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2126 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2126, value203, value556, value642, value655, value656, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2127 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

theorem sound2127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2127 = Sparse.eval value2127 (momentVector H) := by
  have heq : pivotMatrix2127 = (fun u v => node2127 (pivotPermutation2127 u) v) := by apply Matrix.ext; unfold pivotMatrix2127 node2127 pivotPermutation2127; decide +kernel
  have hmoment : injectiveMoment H node2127 = injectiveMoment H pivotMatrix2127 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2127 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2127 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2127 (0 : Fin 5)) =
      Sparse.eval value558 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2127 (0 : Fin 5) = raw2746 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2127 raw2746; decide +kernel
    rw [heq]
    exact (canonical2746 hH).trans (sound558 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2127 (1 : Fin 5)) =
      Sparse.eval value644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2127 (1 : Fin 5) = raw4025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2127 raw4025; decide +kernel
    rw [heq]
    exact (canonical4025 hH).trans (sound644 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2127 (2 : Fin 5)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2127 (2 : Fin 5) = raw4062 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2127 raw4062; decide +kernel
    rw [heq]
    exact (canonical4062 hH).trans (sound206 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2127 (3 : Fin 5)) =
      Sparse.eval value657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2127 (3 : Fin 5) = raw4069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2127 raw4069; decide +kernel
    rw [heq]
    exact (canonical4069 hH).trans (sound657 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2127 (4 : Fin 5)) =
      Sparse.eval value658 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2127 (4 : Fin 5) = raw4070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2127 raw4070; decide +kernel
    rw [heq]
    exact (canonical4070 hH).trans (sound658 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2127 + (injectiveMoment H (mergeFirst pivotMatrix2127 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2127 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2127 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2127 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2127 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2127, value206, value558, value644, value657, value658, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2128 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound2128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2128 = Sparse.eval value2128 (momentVector H) := by
  have heq : pivotMatrix2128 = (fun u v => node2128 (pivotPermutation2128 u) v) := by apply Matrix.ext; unfold pivotMatrix2128 node2128 pivotPermutation2128; decide +kernel
  have hmoment : injectiveMoment H node2128 = injectiveMoment H pivotMatrix2128 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2128 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2128 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2128 (0 : Fin 5)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2128 (0 : Fin 5) = raw2747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2128 raw2747; decide +kernel
    rw [heq]
    exact (canonical2747 hH).trans (sound559 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2128 (1 : Fin 5)) =
      Sparse.eval value645 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2128 (1 : Fin 5) = raw4026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2128 raw4026; decide +kernel
    rw [heq]
    exact (canonical4026 hH).trans (sound645 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2128 (2 : Fin 5)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2128 (2 : Fin 5) = raw4063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2128 raw4063; decide +kernel
    rw [heq]
    exact (canonical4063 hH).trans (sound185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2128 (3 : Fin 5)) =
      Sparse.eval value658 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2128 (3 : Fin 5) = raw4070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2128 raw4070; decide +kernel
    rw [heq]
    exact (canonical4070 hH).trans (sound658 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2128 (4 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2128 (4 : Fin 5) = raw4071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2128 raw4071; decide +kernel
    rw [heq]
    exact (canonical4071 hH).trans (sound659 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2128 + (injectiveMoment H (mergeFirst pivotMatrix2128 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2128 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2128 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2128 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2128 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2128, value185, value559, value645, value658, value659, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2129 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2129 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound2129 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2129 = Sparse.eval value2129 (momentVector H) := by
  have heq : pivotMatrix2129 = (fun u v => node2129 (pivotPermutation2129 u) v) := by apply Matrix.ext; unfold pivotMatrix2129 node2129 pivotPermutation2129; decide +kernel
  have hmoment : injectiveMoment H node2129 = injectiveMoment H pivotMatrix2129 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2129 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2129 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2129 (0 : Fin 5)) =
      Sparse.eval value560 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2129 (0 : Fin 5) = raw2748 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2129 raw2748; decide +kernel
    rw [heq]
    exact (canonical2748 hH).trans (sound560 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2129 (1 : Fin 5)) =
      Sparse.eval value646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2129 (1 : Fin 5) = raw4027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2129 raw4027; decide +kernel
    rw [heq]
    exact (canonical4027 hH).trans (sound646 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2129 (2 : Fin 5)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2129 (2 : Fin 5) = raw4064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2129 raw4064; decide +kernel
    rw [heq]
    exact (canonical4064 hH).trans (sound284 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2129 (3 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2129 (3 : Fin 5) = raw4071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2129 raw4071; decide +kernel
    rw [heq]
    exact (canonical4071 hH).trans (sound659 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2129 (4 : Fin 5)) =
      Sparse.eval value1291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2129 (4 : Fin 5) = raw4072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2129 raw4072; decide +kernel
    rw [heq]
    exact (canonical4072 hH).trans (sound1291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2129 + (injectiveMoment H (mergeFirst pivotMatrix2129 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2129 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2129 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2129 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2129 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2129, value1291, value284, value560, value646, value659, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2130 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem sound2130 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2130 = Sparse.eval value2130 (momentVector H) := by
  have heq : pivotMatrix2130 = (fun u v => node2130 (pivotPermutation2130 u) v) := by apply Matrix.ext; unfold pivotMatrix2130 node2130 pivotPermutation2130; decide +kernel
  have hmoment : injectiveMoment H node2130 = injectiveMoment H pivotMatrix2130 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2130 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2130 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2130 (0 : Fin 5)) =
      Sparse.eval value561 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2130 (0 : Fin 5) = raw2753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2130 raw2753; decide +kernel
    rw [heq]
    exact (canonical2753 hH).trans (sound561 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2130 (1 : Fin 5)) =
      Sparse.eval value647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2130 (1 : Fin 5) = raw4032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2130 raw4032; decide +kernel
    rw [heq]
    exact (canonical4032 hH).trans (sound647 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2130 (2 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2130 (2 : Fin 5) = raw4071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2130 raw4071; decide +kernel
    rw [heq]
    exact (canonical4071 hH).trans (sound659 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2130 (3 : Fin 5)) =
      Sparse.eval value660 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2130 (3 : Fin 5) = raw4076 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2130 raw4076; decide +kernel
    rw [heq]
    exact (canonical4076 hH).trans (sound660 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2130 (4 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2130 (4 : Fin 5) = raw4077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2130 raw4077; decide +kernel
    rw [heq]
    exact (canonical4077 hH).trans (sound661 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2130 + (injectiveMoment H (mergeFirst pivotMatrix2130 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2130 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2130 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2130 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2130 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2130, value561, value647, value659, value660, value661, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2131 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound2131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2131 = Sparse.eval value2131 (momentVector H) := by
  have heq : pivotMatrix2131 = (fun u v => node2131 (pivotPermutation2131 u) v) := by apply Matrix.ext; unfold pivotMatrix2131 node2131 pivotPermutation2131; decide +kernel
  have hmoment : injectiveMoment H node2131 = injectiveMoment H pivotMatrix2131 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2131 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2131 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2131 (0 : Fin 5)) =
      Sparse.eval value562 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2131 (0 : Fin 5) = raw2754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2131 raw2754; decide +kernel
    rw [heq]
    exact (canonical2754 hH).trans (sound562 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2131 (1 : Fin 5)) =
      Sparse.eval value641 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2131 (1 : Fin 5) = raw4033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2131 raw4033; decide +kernel
    rw [heq]
    exact (canonical4033 hH).trans (sound641 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2131 (2 : Fin 5)) =
      Sparse.eval value1291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2131 (2 : Fin 5) = raw4072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2131 raw4072; decide +kernel
    rw [heq]
    exact (canonical4072 hH).trans (sound1291 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2131 (3 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2131 (3 : Fin 5) = raw4077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2131 raw4077; decide +kernel
    rw [heq]
    exact (canonical4077 hH).trans (sound661 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2131 (4 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2131 (4 : Fin 5) = raw4078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2131 raw4078; decide +kernel
    rw [heq]
    exact (canonical4078 hH).trans (sound661 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2131 + (injectiveMoment H (mergeFirst pivotMatrix2131 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2131 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2131 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2131 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2131 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2131, value1291, value562, value641, value661, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2132 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound2132 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2132 = Sparse.eval value2132 (momentVector H) := by
  have heq : pivotMatrix2132 = (fun u v => node2132 (pivotPermutation2132 u) v) := by apply Matrix.ext; unfold pivotMatrix2132 node2132 pivotPermutation2132; decide +kernel
  have hmoment : injectiveMoment H node2132 = injectiveMoment H pivotMatrix2132 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2132 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2132 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2132 (0 : Fin 5)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2132 (0 : Fin 5) = raw2757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2132 raw2757; decide +kernel
    rw [heq]
    exact (canonical2757 hH).trans (sound563 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2132 (1 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2132 (1 : Fin 5) = raw4035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2132 raw4035; decide +kernel
    rw [heq]
    exact (canonical4035 hH).trans (sound648 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2132 (2 : Fin 5)) =
      Sparse.eval value661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2132 (2 : Fin 5) = raw4077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2132 raw4077; decide +kernel
    rw [heq]
    exact (canonical4077 hH).trans (sound661 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2132 (3 : Fin 5)) =
      Sparse.eval value662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2132 (3 : Fin 5) = raw4080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2132 raw4080; decide +kernel
    rw [heq]
    exact (canonical4080 hH).trans (sound662 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2132 (4 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2132 (4 : Fin 5) = raw4081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2132 raw4081; decide +kernel
    rw [heq]
    exact (canonical4081 hH).trans (sound663 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2132 + (injectiveMoment H (mergeFirst pivotMatrix2132 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2132 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2132 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2132 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2132 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2132, value563, value648, value661, value662, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2133 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2133 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

theorem sound2133 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2133 = Sparse.eval value2133 (momentVector H) := by
  have heq : pivotMatrix2133 = (fun u v => node2133 (pivotPermutation2133 u) v) := by apply Matrix.ext; unfold pivotMatrix2133 node2133 pivotPermutation2133; decide +kernel
  have hmoment : injectiveMoment H node2133 = injectiveMoment H pivotMatrix2133 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2133 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2133 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2133 (0 : Fin 5)) =
      Sparse.eval value564 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2133 (0 : Fin 5) = raw2760 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2133 raw2760; decide +kernel
    rw [heq]
    exact (canonical2760 hH).trans (sound564 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2133 (1 : Fin 5)) =
      Sparse.eval value649 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2133 (1 : Fin 5) = raw4038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2133 raw4038; decide +kernel
    rw [heq]
    exact (canonical4038 hH).trans (sound649 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2133 (2 : Fin 5)) =
      Sparse.eval value662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2133 (2 : Fin 5) = raw4080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2133 raw4080; decide +kernel
    rw [heq]
    exact (canonical4080 hH).trans (sound662 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2133 (3 : Fin 5)) =
      Sparse.eval value664 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2133 (3 : Fin 5) = raw4083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2133 raw4083; decide +kernel
    rw [heq]
    exact (canonical4083 hH).trans (sound664 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2133 (4 : Fin 5)) =
      Sparse.eval value665 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2133 (4 : Fin 5) = raw4084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2133 raw4084; decide +kernel
    rw [heq]
    exact (canonical4084 hH).trans (sound665 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2133 + (injectiveMoment H (mergeFirst pivotMatrix2133 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2133 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2133 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2133 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2133 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2133, value564, value649, value662, value664, value665, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2134 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2134 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem sound2134 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2134 = Sparse.eval value2134 (momentVector H) := by
  have heq : pivotMatrix2134 = (fun u v => node2134 (pivotPermutation2134 u) v) := by apply Matrix.ext; unfold pivotMatrix2134 node2134 pivotPermutation2134; decide +kernel
  have hmoment : injectiveMoment H node2134 = injectiveMoment H pivotMatrix2134 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2134 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2134 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2134 (0 : Fin 5)) =
      Sparse.eval value565 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2134 (0 : Fin 5) = raw2761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2134 raw2761; decide +kernel
    rw [heq]
    exact (canonical2761 hH).trans (sound565 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2134 (1 : Fin 5)) =
      Sparse.eval value650 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2134 (1 : Fin 5) = raw4039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2134 raw4039; decide +kernel
    rw [heq]
    exact (canonical4039 hH).trans (sound650 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2134 (2 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2134 (2 : Fin 5) = raw4081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2134 raw4081; decide +kernel
    rw [heq]
    exact (canonical4081 hH).trans (sound663 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2134 (3 : Fin 5)) =
      Sparse.eval value665 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2134 (3 : Fin 5) = raw4084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2134 raw4084; decide +kernel
    rw [heq]
    exact (canonical4084 hH).trans (sound665 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2134 (4 : Fin 5)) =
      Sparse.eval value665 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2134 (4 : Fin 5) = raw4085 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2134 raw4085; decide +kernel
    rw [heq]
    exact (canonical4085 hH).trans (sound665 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2134 + (injectiveMoment H (mergeFirst pivotMatrix2134 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2134 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2134 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2134 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2134 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2134, value565, value650, value663, value665, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2135 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2135 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem sound2135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2135 = Sparse.eval value2135 (momentVector H) := by
  have heq : pivotMatrix2135 = (fun u v => node2135 (pivotPermutation2135 u) v) := by apply Matrix.ext; unfold pivotMatrix2135 node2135 pivotPermutation2135; decide +kernel
  have hmoment : injectiveMoment H node2135 = injectiveMoment H pivotMatrix2135 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2135 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2135 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2135 (0 : Fin 5)) =
      Sparse.eval value566 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2135 (0 : Fin 5) = raw2796 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2135 raw2796; decide +kernel
    rw [heq]
    exact (canonical2796 hH).trans (sound566 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2135 (1 : Fin 5)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2135 (1 : Fin 5) = raw4093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2135 raw4093; decide +kernel
    rw [heq]
    exact (canonical4093 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2135 (2 : Fin 5)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2135 (2 : Fin 5) = raw4107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2135 raw4107; decide +kernel
    rw [heq]
    exact (canonical4107 hH).trans (sound207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2135 (3 : Fin 5)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2135 (3 : Fin 5) = raw4112 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2135 raw4112; decide +kernel
    rw [heq]
    exact (canonical4112 hH).trans (sound207 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2135 (4 : Fin 5)) =
      Sparse.eval value566 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2135 (4 : Fin 5) = raw4113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2135 raw4113; decide +kernel
    rw [heq]
    exact (canonical4113 hH).trans (sound566 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2135 + (injectiveMoment H (mergeFirst pivotMatrix2135 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2135 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2135 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2135 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2135 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2135, value207, value566, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2136 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound2136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2136 = Sparse.eval value2136 (momentVector H) := by
  have heq : pivotMatrix2136 = (fun u v => node2136 (pivotPermutation2136 u) v) := by apply Matrix.ext; unfold pivotMatrix2136 node2136 pivotPermutation2136; decide +kernel
  have hmoment : injectiveMoment H node2136 = injectiveMoment H pivotMatrix2136 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2136 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2136 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2136 (0 : Fin 5)) =
      Sparse.eval value569 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2136 (0 : Fin 5) = raw2799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2136 raw2799; decide +kernel
    rw [heq]
    exact (canonical2799 hH).trans (sound569 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2136 (1 : Fin 5)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2136 (1 : Fin 5) = raw4094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2136 raw4094; decide +kernel
    rw [heq]
    exact (canonical4094 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2136 (2 : Fin 5)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2136 (2 : Fin 5) = raw4108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2136 raw4108; decide +kernel
    rw [heq]
    exact (canonical4108 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2136 (3 : Fin 5)) =
      Sparse.eval value666 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2136 (3 : Fin 5) = raw4114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2136 raw4114; decide +kernel
    rw [heq]
    exact (canonical4114 hH).trans (sound666 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2136 (4 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2136 (4 : Fin 5) = raw4115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2136 raw4115; decide +kernel
    rw [heq]
    exact (canonical4115 hH).trans (sound667 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2136 + (injectiveMoment H (mergeFirst pivotMatrix2136 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2136 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2136 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2136 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2136 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2136, value210, value569, value666, value667, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2137 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2137 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound2137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2137 = Sparse.eval value2137 (momentVector H) := by
  have heq : pivotMatrix2137 = (fun u v => node2137 (pivotPermutation2137 u) v) := by apply Matrix.ext; unfold pivotMatrix2137 node2137 pivotPermutation2137; decide +kernel
  have hmoment : injectiveMoment H node2137 = injectiveMoment H pivotMatrix2137 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2137 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2137 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2137 (0 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2137 (0 : Fin 5) = raw2800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2137 raw2800; decide +kernel
    rw [heq]
    exact (canonical2800 hH).trans (sound570 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2137 (1 : Fin 5)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2137 (1 : Fin 5) = raw4095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2137 raw4095; decide +kernel
    rw [heq]
    exact (canonical4095 hH).trans (sound294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2137 (2 : Fin 5)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2137 (2 : Fin 5) = raw4109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2137 raw4109; decide +kernel
    rw [heq]
    exact (canonical4109 hH).trans (sound294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2137 (3 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2137 (3 : Fin 5) = raw4115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2137 raw4115; decide +kernel
    rw [heq]
    exact (canonical4115 hH).trans (sound667 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2137 (4 : Fin 5)) =
      Sparse.eval value668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2137 (4 : Fin 5) = raw4116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2137 raw4116; decide +kernel
    rw [heq]
    exact (canonical4116 hH).trans (sound668 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2137 + (injectiveMoment H (mergeFirst pivotMatrix2137 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2137 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2137 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2137 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2137 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2137, value294, value570, value667, value668, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2138 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2138 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

theorem sound2138 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2138 = Sparse.eval value2138 (momentVector H) := by
  have heq : pivotMatrix2138 = (fun u v => node2138 (pivotPermutation2138 u) v) := by apply Matrix.ext; unfold pivotMatrix2138 node2138 pivotPermutation2138; decide +kernel
  have hmoment : injectiveMoment H node2138 = injectiveMoment H pivotMatrix2138 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2138 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2138 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2138 (0 : Fin 5)) =
      Sparse.eval value572 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2138 (0 : Fin 5) = raw2808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2138 raw2808; decide +kernel
    rw [heq]
    exact (canonical2808 hH).trans (sound572 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2138 (1 : Fin 5)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2138 (1 : Fin 5) = raw4097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2138 raw4097; decide +kernel
    rw [heq]
    exact (canonical4097 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2138 (2 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2138 (2 : Fin 5) = raw4115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2138 raw4115; decide +kernel
    rw [heq]
    exact (canonical4115 hH).trans (sound667 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2138 (3 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2138 (3 : Fin 5) = raw4120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2138 raw4120; decide +kernel
    rw [heq]
    exact (canonical4120 hH).trans (sound669 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2138 (4 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2138 (4 : Fin 5) = raw4121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2138 raw4121; decide +kernel
    rw [heq]
    exact (canonical4121 hH).trans (sound670 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2138 + (injectiveMoment H (mergeFirst pivotMatrix2138 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2138 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2138 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2138 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2138 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2138, value203, value572, value667, value669, value670, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2139 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem sound2139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2139 = Sparse.eval value2139 (momentVector H) := by
  have heq : pivotMatrix2139 = (fun u v => node2139 (pivotPermutation2139 u) v) := by apply Matrix.ext; unfold pivotMatrix2139 node2139 pivotPermutation2139; decide +kernel
  have hmoment : injectiveMoment H node2139 = injectiveMoment H pivotMatrix2139 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2139 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2139 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2139 (0 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2139 (0 : Fin 5) = raw2809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2139 raw2809; decide +kernel
    rw [heq]
    exact (canonical2809 hH).trans (sound573 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2139 (1 : Fin 5)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2139 (1 : Fin 5) = raw4098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2139 raw4098; decide +kernel
    rw [heq]
    exact (canonical4098 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2139 (2 : Fin 5)) =
      Sparse.eval value668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2139 (2 : Fin 5) = raw4116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2139 raw4116; decide +kernel
    rw [heq]
    exact (canonical4116 hH).trans (sound668 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2139 (3 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2139 (3 : Fin 5) = raw4121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2139 raw4121; decide +kernel
    rw [heq]
    exact (canonical4121 hH).trans (sound670 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2139 (4 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2139 (4 : Fin 5) = raw4122 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2139 raw4122; decide +kernel
    rw [heq]
    exact (canonical4122 hH).trans (sound670 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2139 + (injectiveMoment H (mergeFirst pivotMatrix2139 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2139 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2139 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2139 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2139 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2139, value207, value573, value668, value670, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2140 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem sound2140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2140 = Sparse.eval value2140 (momentVector H) := by
  have heq : pivotMatrix2140 = (fun u v => node2140 (pivotPermutation2140 u) v) := by apply Matrix.ext; unfold pivotMatrix2140 node2140 pivotPermutation2140; decide +kernel
  have hmoment : injectiveMoment H node2140 = injectiveMoment H pivotMatrix2140 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2140 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2140 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2140 (0 : Fin 5)) =
      Sparse.eval value575 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2140 (0 : Fin 5) = raw2813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2140 raw2813; decide +kernel
    rw [heq]
    exact (canonical2813 hH).trans (sound575 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2140 (1 : Fin 5)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2140 (1 : Fin 5) = raw4100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2140 raw4100; decide +kernel
    rw [heq]
    exact (canonical4100 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2140 (2 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2140 (2 : Fin 5) = raw4121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2140 raw4121; decide +kernel
    rw [heq]
    exact (canonical4121 hH).trans (sound670 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2140 (3 : Fin 5)) =
      Sparse.eval value671 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2140 (3 : Fin 5) = raw4124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2140 raw4124; decide +kernel
    rw [heq]
    exact (canonical4124 hH).trans (sound671 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2140 (4 : Fin 5)) =
      Sparse.eval value672 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2140 (4 : Fin 5) = raw4125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2140 raw4125; decide +kernel
    rw [heq]
    exact (canonical4125 hH).trans (sound672 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2140 + (injectiveMoment H (mergeFirst pivotMatrix2140 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2140 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2140 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2140 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2140 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2140, value215, value575, value670, value671, value672, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2141 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

theorem sound2141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2141 = Sparse.eval value2141 (momentVector H) := by
  have heq : pivotMatrix2141 = (fun u v => node2141 (pivotPermutation2141 u) v) := by apply Matrix.ext; unfold pivotMatrix2141 node2141 pivotPermutation2141; decide +kernel
  have hmoment : injectiveMoment H node2141 = injectiveMoment H pivotMatrix2141 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2141 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2141 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2141 (0 : Fin 5)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2141 (0 : Fin 5) = raw4951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2141 raw4951; decide +kernel
    rw [heq]
    exact (canonical4951 hH).trans (sound708 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2141 (1 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2141 (1 : Fin 5) = raw4136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2141 raw4136; decide +kernel
    rw [heq]
    exact (canonical4136 hH).trans (sound669 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2141 (2 : Fin 5)) =
      Sparse.eval value669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2141 (2 : Fin 5) = raw4120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2141 raw4120; decide +kernel
    rw [heq]
    exact (canonical4120 hH).trans (sound669 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2141 (3 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2141 (3 : Fin 5) = raw4115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2141 raw4115; decide +kernel
    rw [heq]
    exact (canonical4115 hH).trans (sound667 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2141 (4 : Fin 5)) =
      Sparse.eval value666 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2141 (4 : Fin 5) = raw4114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2141 raw4114; decide +kernel
    rw [heq]
    exact (canonical4114 hH).trans (sound666 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2141 + (injectiveMoment H (mergeFirst pivotMatrix2141 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2141 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2141 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2141 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2141 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2141, value666, value667, value669, value708, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2142 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

theorem sound2142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2142 = Sparse.eval value2142 (momentVector H) := by
  have heq : pivotMatrix2142 = (fun u v => node2142 (pivotPermutation2142 u) v) := by apply Matrix.ext; unfold pivotMatrix2142 node2142 pivotPermutation2142; decide +kernel
  have hmoment : injectiveMoment H node2142 = injectiveMoment H pivotMatrix2142 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2142 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2142 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2142 (0 : Fin 5)) =
      Sparse.eval value709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2142 (0 : Fin 5) = raw4952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2142 raw4952; decide +kernel
    rw [heq]
    exact (canonical4952 hH).trans (sound709 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2142 (1 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2142 (1 : Fin 5) = raw4137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2142 raw4137; decide +kernel
    rw [heq]
    exact (canonical4137 hH).trans (sound670 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2142 (2 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2142 (2 : Fin 5) = raw4121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2142 raw4121; decide +kernel
    rw [heq]
    exact (canonical4121 hH).trans (sound670 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2142 (3 : Fin 5)) =
      Sparse.eval value668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2142 (3 : Fin 5) = raw4116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2142 raw4116; decide +kernel
    rw [heq]
    exact (canonical4116 hH).trans (sound668 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2142 (4 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2142 (4 : Fin 5) = raw4115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2142 raw4115; decide +kernel
    rw [heq]
    exact (canonical4115 hH).trans (sound667 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2142 + (injectiveMoment H (mergeFirst pivotMatrix2142 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2142 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2142 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2142 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2142 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2142, value667, value668, value670, value709, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2143 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2143 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem sound2143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2143 = Sparse.eval value2143 (momentVector H) := by
  have heq : pivotMatrix2143 = (fun u v => node2143 (pivotPermutation2143 u) v) := by apply Matrix.ext; unfold pivotMatrix2143 node2143 pivotPermutation2143; decide +kernel
  have hmoment : injectiveMoment H node2143 = injectiveMoment H pivotMatrix2143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2143 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2143 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2143 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2143 (0 : Fin 4) = raw6916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2143 raw6916; decide +kernel
    rw [heq]
    exact (canonical6916 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2143 (1 : Fin 4)) =
      Sparse.eval value403 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2143 (1 : Fin 4) = raw4206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2143 raw4206; decide +kernel
    rw [heq]
    exact (canonical4206 hH).trans (sound403 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2143 (2 : Fin 4)) =
      Sparse.eval value997 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2143 (2 : Fin 4) = raw4185 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2143 raw4185; decide +kernel
    rw [heq]
    exact (canonical4185 hH).trans (sound997 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2143 (3 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2143 (3 : Fin 4) = raw4184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2143 raw4184; decide +kernel
    rw [heq]
    exact (canonical4184 hH).trans (sound1164 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2143 + (injectiveMoment H (mergeFirst pivotMatrix2143 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2143 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2143 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2143 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2143, value1164, value403, value996, value997, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2144 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2144 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound2144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2144 = Sparse.eval value2144 (momentVector H) := by
  have heq : pivotMatrix2144 = (fun u v => node2144 (pivotPermutation2144 u) v) := by apply Matrix.ext; unfold pivotMatrix2144 node2144 pivotPermutation2144; decide +kernel
  have hmoment : injectiveMoment H node2144 = injectiveMoment H pivotMatrix2144 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2144 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2144 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2144 (0 : Fin 4)) =
      Sparse.eval value1064 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (0 : Fin 4) = raw5077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw5077; decide +kernel
    rw [heq]
    exact (canonical5077 hH).trans (sound1064 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2144 (1 : Fin 4)) =
      Sparse.eval value1065 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (1 : Fin 4) = raw4225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw4225; decide +kernel
    rw [heq]
    exact (canonical4225 hH).trans (sound1065 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2144 (2 : Fin 4)) =
      Sparse.eval value780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (2 : Fin 4) = raw4218 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw4218; decide +kernel
    rw [heq]
    exact (canonical4218 hH).trans (sound780 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2144 (3 : Fin 4)) =
      Sparse.eval value1158 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2144 (3 : Fin 4) = raw4217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2144 raw4217; decide +kernel
    rw [heq]
    exact (canonical4217 hH).trans (sound1158 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2144 + (injectiveMoment H (mergeFirst pivotMatrix2144 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2144 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2144 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2144 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2144, value1064, value1065, value1158, value780, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2145 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2145 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound2145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2145 = Sparse.eval value2145 (momentVector H) := by
  have heq : pivotMatrix2145 = (fun u v => node2145 (pivotPermutation2145 u) v) := by apply Matrix.ext; unfold pivotMatrix2145 node2145 pivotPermutation2145; decide +kernel
  have hmoment : injectiveMoment H node2145 = injectiveMoment H pivotMatrix2145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2145 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2145 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2145 (0 : Fin 4)) =
      Sparse.eval value713 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2145 (0 : Fin 4) = raw5082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2145 raw5082; decide +kernel
    rw [heq]
    exact (canonical5082 hH).trans (sound713 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2145 (1 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2145 (1 : Fin 4) = raw4230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2145 raw4230; decide +kernel
    rw [heq]
    exact (canonical4230 hH).trans (sound1056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2145 (2 : Fin 4)) =
      Sparse.eval value1001 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2145 (2 : Fin 4) = raw4223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2145 raw4223; decide +kernel
    rw [heq]
    exact (canonical4223 hH).trans (sound1001 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2145 (3 : Fin 4)) =
      Sparse.eval value494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2145 (3 : Fin 4) = raw4222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2145 raw4222; decide +kernel
    rw [heq]
    exact (canonical4222 hH).trans (sound494 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2145 + (injectiveMoment H (mergeFirst pivotMatrix2145 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2145 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2145 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2145 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2145, value1001, value1056, value494, value713, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2146 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2146 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 1, 0, -2]]

theorem sound2146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2146 = Sparse.eval value2146 (momentVector H) := by
  have heq : pivotMatrix2146 = (fun u v => node2146 (pivotPermutation2146 u) v) := by apply Matrix.ext; unfold pivotMatrix2146 node2146 pivotPermutation2146; decide +kernel
  have hmoment : injectiveMoment H node2146 = injectiveMoment H pivotMatrix2146 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2146 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2146 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2146 (0 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (0 : Fin 4) = raw5095 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw5095; decide +kernel
    rw [heq]
    exact (canonical5095 hH).trans (sound593 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2146 (1 : Fin 4)) =
      Sparse.eval value598 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (1 : Fin 4) = raw4232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw4232; decide +kernel
    rw [heq]
    exact (canonical4232 hH).trans (sound598 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2146 (2 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (2 : Fin 4) = raw4230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw4230; decide +kernel
    rw [heq]
    exact (canonical4230 hH).trans (sound1056 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2146 (3 : Fin 4)) =
      Sparse.eval value480 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2146 (3 : Fin 4) = raw4229 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2146 raw4229; decide +kernel
    rw [heq]
    exact (canonical4229 hH).trans (sound480 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2146 + (injectiveMoment H (mergeFirst pivotMatrix2146 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2146 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2146 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2146 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2146, value1056, value480, value593, value598, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2147 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2147 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

theorem sound2147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2147 = Sparse.eval value2147 (momentVector H) := by
  have heq : pivotMatrix2147 = (fun u v => node2147 (pivotPermutation2147 u) v) := by apply Matrix.ext; unfold pivotMatrix2147 node2147 pivotPermutation2147; decide +kernel
  have hmoment : injectiveMoment H node2147 = injectiveMoment H pivotMatrix2147 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2147 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2147 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2147 (0 : Fin 4)) =
      Sparse.eval value918 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2147 (0 : Fin 4) = raw5099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2147 raw5099; decide +kernel
    rw [heq]
    exact (canonical5099 hH).trans (sound918 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2147 (1 : Fin 4)) =
      Sparse.eval value783 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2147 (1 : Fin 4) = raw4239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2147 raw4239; decide +kernel
    rw [heq]
    exact (canonical4239 hH).trans (sound783 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2147 (2 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2147 (2 : Fin 4) = raw4238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2147 raw4238; decide +kernel
    rw [heq]
    exact (canonical4238 hH).trans (sound977 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2147 (3 : Fin 4)) =
      Sparse.eval value778 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2147 (3 : Fin 4) = raw4237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2147 raw4237; decide +kernel
    rw [heq]
    exact (canonical4237 hH).trans (sound778 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2147 + (injectiveMoment H (mergeFirst pivotMatrix2147 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2147 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2147 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2147 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2147, value778, value783, value918, value977, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2148 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2148 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound2148 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2148 = Sparse.eval value2148 (momentVector H) := by
  have heq : pivotMatrix2148 = (fun u v => node2148 (pivotPermutation2148 u) v) := by apply Matrix.ext; unfold pivotMatrix2148 node2148 pivotPermutation2148; decide +kernel
  have hmoment : injectiveMoment H node2148 = injectiveMoment H pivotMatrix2148 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2148 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2148 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2148 (0 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2148 (0 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2148 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2148 (1 : Fin 4)) =
      Sparse.eval value1026 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2148 (1 : Fin 4) = raw4254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2148 raw4254; decide +kernel
    rw [heq]
    exact (canonical4254 hH).trans (sound1026 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2148 (2 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2148 (2 : Fin 4) = raw4250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2148 raw4250; decide +kernel
    rw [heq]
    exact (canonical4250 hH).trans (sound466 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2148 (3 : Fin 4)) =
      Sparse.eval value1091 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2148 (3 : Fin 4) = raw4249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2148 raw4249; decide +kernel
    rw [heq]
    exact (canonical4249 hH).trans (sound1091 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2148 + (injectiveMoment H (mergeFirst pivotMatrix2148 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2148 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2148 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2148 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2148, value1026, value1036, value1091, value466, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2149 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2149 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound2149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2149 = Sparse.eval value2149 (momentVector H) := by
  have heq : pivotMatrix2149 = (fun u v => node2149 (pivotPermutation2149 u) v) := by apply Matrix.ext; unfold pivotMatrix2149 node2149 pivotPermutation2149; decide +kernel
  have hmoment : injectiveMoment H node2149 = injectiveMoment H pivotMatrix2149 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2149 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2149 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2149 (0 : Fin 4)) =
      Sparse.eval value993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2149 (0 : Fin 4) = raw5219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2149 raw5219; decide +kernel
    rw [heq]
    exact (canonical5219 hH).trans (sound993 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2149 (1 : Fin 4)) =
      Sparse.eval value994 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2149 (1 : Fin 4) = raw4272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2149 raw4272; decide +kernel
    rw [heq]
    exact (canonical4272 hH).trans (sound994 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2149 (2 : Fin 4)) =
      Sparse.eval value762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2149 (2 : Fin 4) = raw4251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2149 raw4251; decide +kernel
    rw [heq]
    exact (canonical4251 hH).trans (sound762 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2149 (3 : Fin 4)) =
      Sparse.eval value1091 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2149 (3 : Fin 4) = raw4249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2149 raw4249; decide +kernel
    rw [heq]
    exact (canonical4249 hH).trans (sound1091 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2149 + (injectiveMoment H (mergeFirst pivotMatrix2149 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2149 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2149 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2149 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2149, value1091, value762, value993, value994, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2150 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2150 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound2150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2150 = Sparse.eval value2150 (momentVector H) := by
  have heq : pivotMatrix2150 = (fun u v => node2150 (pivotPermutation2150 u) v) := by apply Matrix.ext; unfold pivotMatrix2150 node2150 pivotPermutation2150; decide +kernel
  have hmoment : injectiveMoment H node2150 = injectiveMoment H pivotMatrix2150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2150 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2150 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2150 (0 : Fin 4)) =
      Sparse.eval value931 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2150 (0 : Fin 4) = raw5220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2150 raw5220; decide +kernel
    rw [heq]
    exact (canonical5220 hH).trans (sound931 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2150 (1 : Fin 4)) =
      Sparse.eval value764 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2150 (1 : Fin 4) = raw4273 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2150 raw4273; decide +kernel
    rw [heq]
    exact (canonical4273 hH).trans (sound764 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2150 (2 : Fin 4)) =
      Sparse.eval value762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2150 (2 : Fin 4) = raw4252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2150 raw4252; decide +kernel
    rw [heq]
    exact (canonical4252 hH).trans (sound762 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2150 (3 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2150 (3 : Fin 4) = raw4250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2150 raw4250; decide +kernel
    rw [heq]
    exact (canonical4250 hH).trans (sound466 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2150 + (injectiveMoment H (mergeFirst pivotMatrix2150 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2150 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2150 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2150 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2150, value466, value762, value764, value931, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2151 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2151 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2151 = Sparse.eval value2151 (momentVector H) := by
  have heq : pivotMatrix2151 = (fun u v => node2151 (pivotPermutation2151 u) v) := by apply Matrix.ext; unfold pivotMatrix2151 node2151 pivotPermutation2151; decide +kernel
  have hmoment : injectiveMoment H node2151 = injectiveMoment H pivotMatrix2151 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2151 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2151 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2151 (0 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2151 (0 : Fin 4) = raw6998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2151 raw6998; decide +kernel
    rw [heq]
    exact (canonical6998 hH).trans (sound1171 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2151 (1 : Fin 4)) =
      Sparse.eval value785 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2151 (1 : Fin 4) = raw4289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2151 raw4289; decide +kernel
    rw [heq]
    exact (canonical4289 hH).trans (sound785 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2151 (2 : Fin 4)) =
      Sparse.eval value762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2151 (2 : Fin 4) = raw4252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2151 raw4252; decide +kernel
    rw [heq]
    exact (canonical4252 hH).trans (sound762 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2151 (3 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2151 (3 : Fin 4) = raw4248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2151 raw4248; decide +kernel
    rw [heq]
    exact (canonical4248 hH).trans (sound460 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2151 + (injectiveMoment H (mergeFirst pivotMatrix2151 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2151 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2151 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2151 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2151, value1171, value460, value762, value785, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2152 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2152 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound2152 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2152 = Sparse.eval value2152 (momentVector H) := by
  have heq : pivotMatrix2152 = (fun u v => node2152 (pivotPermutation2152 u) v) := by apply Matrix.ext; unfold pivotMatrix2152 node2152 pivotPermutation2152; decide +kernel
  have hmoment : injectiveMoment H node2152 = injectiveMoment H pivotMatrix2152 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2152 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2152 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2152 (0 : Fin 4)) =
      Sparse.eval value1024 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2152 (0 : Fin 4) = raw5221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2152 raw5221; decide +kernel
    rw [heq]
    exact (canonical5221 hH).trans (sound1024 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2152 (1 : Fin 4)) =
      Sparse.eval value1023 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2152 (1 : Fin 4) = raw4277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2152 raw4277; decide +kernel
    rw [heq]
    exact (canonical4277 hH).trans (sound1023 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2152 (2 : Fin 4)) =
      Sparse.eval value905 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2152 (2 : Fin 4) = raw4255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2152 raw4255; decide +kernel
    rw [heq]
    exact (canonical4255 hH).trans (sound905 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2152 (3 : Fin 4)) =
      Sparse.eval value1026 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2152 (3 : Fin 4) = raw4254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2152 raw4254; decide +kernel
    rw [heq]
    exact (canonical4254 hH).trans (sound1026 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2152 + (injectiveMoment H (mergeFirst pivotMatrix2152 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2152 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2152 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2152 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2152, value1023, value1024, value1026, value905, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2153 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2153 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem sound2153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2153 = Sparse.eval value2153 (momentVector H) := by
  have heq : pivotMatrix2153 = (fun u v => node2153 (pivotPermutation2153 u) v) := by apply Matrix.ext; unfold pivotMatrix2153 node2153 pivotPermutation2153; decide +kernel
  have hmoment : injectiveMoment H node2153 = injectiveMoment H pivotMatrix2153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2153 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2153 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2153 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (0 : Fin 4) = raw4373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4373; decide +kernel
    rw [heq]
    exact (canonical4373 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2153 (1 : Fin 4)) =
      Sparse.eval value776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (1 : Fin 4) = raw4268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4268; decide +kernel
    rw [heq]
    exact (canonical4268 hH).trans (sound776 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2153 (2 : Fin 4)) =
      Sparse.eval value770 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (2 : Fin 4) = raw4262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4262; decide +kernel
    rw [heq]
    exact (canonical4262 hH).trans (sound770 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2153 (3 : Fin 4)) =
      Sparse.eval value913 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2153 (3 : Fin 4) = raw4260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2153 raw4260; decide +kernel
    rw [heq]
    exact (canonical4260 hH).trans (sound913 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2153 + (injectiveMoment H (mergeFirst pivotMatrix2153 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2153 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2153 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2153 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2153, value770, value776, value913, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2154 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2154 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem sound2154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2154 = Sparse.eval value2154 (momentVector H) := by
  have heq : pivotMatrix2154 = (fun u v => node2154 (pivotPermutation2154 u) v) := by apply Matrix.ext; unfold pivotMatrix2154 node2154 pivotPermutation2154; decide +kernel
  have hmoment : injectiveMoment H node2154 = injectiveMoment H pivotMatrix2154 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2154 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2154 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2154 (0 : Fin 4)) =
      Sparse.eval value804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (0 : Fin 4) = raw4377 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4377; decide +kernel
    rw [heq]
    exact (canonical4377 hH).trans (sound804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2154 (1 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (1 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2154 (2 : Fin 4)) =
      Sparse.eval value1162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (2 : Fin 4) = raw4264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4264; decide +kernel
    rw [heq]
    exact (canonical4264 hH).trans (sound1162 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2154 (3 : Fin 4)) =
      Sparse.eval value770 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2154 (3 : Fin 4) = raw4262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2154 raw4262; decide +kernel
    rw [heq]
    exact (canonical4262 hH).trans (sound770 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2154 + (injectiveMoment H (mergeFirst pivotMatrix2154 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2154 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2154 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2154 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2154, value1162, value394, value770, value804, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2155 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2155 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

theorem sound2155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2155 = Sparse.eval value2155 (momentVector H) := by
  have heq : pivotMatrix2155 = (fun u v => node2155 (pivotPermutation2155 u) v) := by apply Matrix.ext; unfold pivotMatrix2155 node2155 pivotPermutation2155; decide +kernel
  have hmoment : injectiveMoment H node2155 = injectiveMoment H pivotMatrix2155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2155 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2155 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2155 (0 : Fin 4)) =
      Sparse.eval value808 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (0 : Fin 4) = raw4394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4394; decide +kernel
    rw [heq]
    exact (canonical4394 hH).trans (sound808 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2155 (1 : Fin 4)) =
      Sparse.eval value1184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (1 : Fin 4) = raw4276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4276; decide +kernel
    rw [heq]
    exact (canonical4276 hH).trans (sound1184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2155 (2 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (2 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2155 (3 : Fin 4)) =
      Sparse.eval value776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2155 (3 : Fin 4) = raw4268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2155 raw4268; decide +kernel
    rw [heq]
    exact (canonical4268 hH).trans (sound776 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2155 + (injectiveMoment H (mergeFirst pivotMatrix2155 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2155 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2155 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2155 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2155, value1184, value394, value776, value808, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2156 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2156 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem sound2156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2156 = Sparse.eval value2156 (momentVector H) := by
  have heq : pivotMatrix2156 = (fun u v => node2156 (pivotPermutation2156 u) v) := by apply Matrix.ext; unfold pivotMatrix2156 node2156 pivotPermutation2156; decide +kernel
  have hmoment : injectiveMoment H node2156 = injectiveMoment H pivotMatrix2156 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2156 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2156 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2156 (0 : Fin 4)) =
      Sparse.eval value973 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2156 (0 : Fin 4) = raw4421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2156 raw4421; decide +kernel
    rw [heq]
    exact (canonical4421 hH).trans (sound973 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2156 (1 : Fin 4)) =
      Sparse.eval value785 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2156 (1 : Fin 4) = raw4283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2156 raw4283; decide +kernel
    rw [heq]
    exact (canonical4283 hH).trans (sound785 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2156 (2 : Fin 4)) =
      Sparse.eval value918 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2156 (2 : Fin 4) = raw4280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2156 raw4280; decide +kernel
    rw [heq]
    exact (canonical4280 hH).trans (sound918 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2156 (3 : Fin 4)) =
      Sparse.eval value788 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2156 (3 : Fin 4) = raw4279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2156 raw4279; decide +kernel
    rw [heq]
    exact (canonical4279 hH).trans (sound788 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2156 + (injectiveMoment H (mergeFirst pivotMatrix2156 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2156 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2156 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2156 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2156, value785, value788, value918, value973, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2157 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2157 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound2157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2157 = Sparse.eval value2157 (momentVector H) := by
  have heq : pivotMatrix2157 = (fun u v => node2157 (pivotPermutation2157 u) v) := by apply Matrix.ext; unfold pivotMatrix2157 node2157 pivotPermutation2157; decide +kernel
  have hmoment : injectiveMoment H node2157 = injectiveMoment H pivotMatrix2157 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2157 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2157 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2157 (0 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2157 (0 : Fin 4) = raw4429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2157 raw4429; decide +kernel
    rw [heq]
    exact (canonical4429 hH).trans (sound995 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2157 (1 : Fin 4)) =
      Sparse.eval value992 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2157 (1 : Fin 4) = raw4286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2157 raw4286; decide +kernel
    rw [heq]
    exact (canonical4286 hH).trans (sound992 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2157 (2 : Fin 4)) =
      Sparse.eval value463 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2157 (2 : Fin 4) = raw4285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2157 raw4285; decide +kernel
    rw [heq]
    exact (canonical4285 hH).trans (sound463 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2157 (3 : Fin 4)) =
      Sparse.eval value1236 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2157 (3 : Fin 4) = raw4284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2157 raw4284; decide +kernel
    rw [heq]
    exact (canonical4284 hH).trans (sound1236 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2157 + (injectiveMoment H (mergeFirst pivotMatrix2157 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2157 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2157 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2157 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2157, value1236, value463, value992, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2158 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2158 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound2158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2158 = Sparse.eval value2158 (momentVector H) := by
  have heq : pivotMatrix2158 = (fun u v => node2158 (pivotPermutation2158 u) v) := by apply Matrix.ext; unfold pivotMatrix2158 node2158 pivotPermutation2158; decide +kernel
  have hmoment : injectiveMoment H node2158 = injectiveMoment H pivotMatrix2158 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2158 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2158 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2158 (0 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2158 (0 : Fin 4) = raw4432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2158 raw4432; decide +kernel
    rw [heq]
    exact (canonical4432 hH).trans (sound1028 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2158 (1 : Fin 4)) =
      Sparse.eval value1022 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2158 (1 : Fin 4) = raw4288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2158 raw4288; decide +kernel
    rw [heq]
    exact (canonical4288 hH).trans (sound1022 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2158 (2 : Fin 4)) =
      Sparse.eval value992 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2158 (2 : Fin 4) = raw4287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2158 raw4287; decide +kernel
    rw [heq]
    exact (canonical4287 hH).trans (sound992 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2158 (3 : Fin 4)) =
      Sparse.eval value992 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2158 (3 : Fin 4) = raw4286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2158 raw4286; decide +kernel
    rw [heq]
    exact (canonical4286 hH).trans (sound992 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2158 + (injectiveMoment H (mergeFirst pivotMatrix2158 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2158 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2158 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2158 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2158, value1022, value1028, value992, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2159 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2159 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem sound2159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2159 = Sparse.eval value2159 (momentVector H) := by
  have heq : pivotMatrix2159 = (fun u v => node2159 (pivotPermutation2159 u) v) := by apply Matrix.ext; unfold pivotMatrix2159 node2159 pivotPermutation2159; decide +kernel
  have hmoment : injectiveMoment H node2159 = injectiveMoment H pivotMatrix2159 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2159 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2159 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2159 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2159 (0 : Fin 4) = raw7019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2159 raw7019; decide +kernel
    rw [heq]
    exact (canonical7019 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2159 (1 : Fin 4)) =
      Sparse.eval value1236 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2159 (1 : Fin 4) = raw4290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2159 raw4290; decide +kernel
    rw [heq]
    exact (canonical4290 hH).trans (sound1236 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2159 (2 : Fin 4)) =
      Sparse.eval value994 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2159 (2 : Fin 4) = raw4274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2159 raw4274; decide +kernel
    rw [heq]
    exact (canonical4274 hH).trans (sound994 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2159 (3 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2159 (3 : Fin 4) = raw4270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2159 raw4270; decide +kernel
    rw [heq]
    exact (canonical4270 hH).trans (sound394 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2159 + (injectiveMoment H (mergeFirst pivotMatrix2159 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2159 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2159 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2159 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2159, value1178, value1236, value394, value994, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2160 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2160 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound2160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2160 = Sparse.eval value2160 (momentVector H) := by
  have heq : pivotMatrix2160 = (fun u v => node2160 (pivotPermutation2160 u) v) := by apply Matrix.ext; unfold pivotMatrix2160 node2160 pivotPermutation2160; decide +kernel
  have hmoment : injectiveMoment H node2160 = injectiveMoment H pivotMatrix2160 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2160 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2160 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2160 (0 : Fin 4)) =
      Sparse.eval value1021 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2160 (0 : Fin 4) = raw5232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2160 raw5232; decide +kernel
    rw [heq]
    exact (canonical5232 hH).trans (sound1021 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2160 (1 : Fin 4)) =
      Sparse.eval value1022 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2160 (1 : Fin 4) = raw4288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2160 raw4288; decide +kernel
    rw [heq]
    exact (canonical4288 hH).trans (sound1022 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2160 (2 : Fin 4)) =
      Sparse.eval value1023 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2160 (2 : Fin 4) = raw4278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2160 raw4278; decide +kernel
    rw [heq]
    exact (canonical4278 hH).trans (sound1023 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2160 (3 : Fin 4)) =
      Sparse.eval value1023 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2160 (3 : Fin 4) = raw4277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2160 raw4277; decide +kernel
    rw [heq]
    exact (canonical4277 hH).trans (sound1023 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2160 + (injectiveMoment H (mergeFirst pivotMatrix2160 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2160 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2160 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2160 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2160, value1021, value1022, value1023, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2161 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2161 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound2161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2161 = Sparse.eval value2161 (momentVector H) := by
  have heq : pivotMatrix2161 = (fun u v => node2161 (pivotPermutation2161 u) v) := by apply Matrix.ext; unfold pivotMatrix2161 node2161 pivotPermutation2161; decide +kernel
  have hmoment : injectiveMoment H node2161 = injectiveMoment H pivotMatrix2161 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2161 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2161 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2161 (0 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2161 (0 : Fin 4) = raw3134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2161 raw3134; decide +kernel
    rw [heq]
    exact (canonical3134 hH).trans (sound936 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2161 (1 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2161 (1 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2161 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2161 (2 : Fin 4)) =
      Sparse.eval value983 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2161 (2 : Fin 4) = raw4383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2161 raw4383; decide +kernel
    rw [heq]
    exact (canonical4383 hH).trans (sound983 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2161 (3 : Fin 4)) =
      Sparse.eval value964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2161 (3 : Fin 4) = raw4385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2161 raw4385; decide +kernel
    rw [heq]
    exact (canonical4385 hH).trans (sound964 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2161 + (injectiveMoment H (mergeFirst pivotMatrix2161 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2161 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2161 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2161 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2161, value502, value936, value964, value983, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2162 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2162 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 1, -2, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2162 = Sparse.eval value2162 (momentVector H) := by
  have heq : pivotMatrix2162 = (fun u v => node2162 (pivotPermutation2162 u) v) := by apply Matrix.ext; unfold pivotMatrix2162 node2162 pivotPermutation2162; decide +kernel
  have hmoment : injectiveMoment H node2162 = injectiveMoment H pivotMatrix2162 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2162 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2162 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2162 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2162 (0 : Fin 4) = raw3156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2162 raw3156; decide +kernel
    rw [heq]
    exact (canonical3156 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2162 (1 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2162 (1 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2162 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2162 (2 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2162 (2 : Fin 4) = raw4399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2162 raw4399; decide +kernel
    rw [heq]
    exact (canonical4399 hH).trans (sound484 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2162 (3 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2162 (3 : Fin 4) = raw4401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2162 raw4401; decide +kernel
    rw [heq]
    exact (canonical4401 hH).trans (sound1032 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2162 + (injectiveMoment H (mergeFirst pivotMatrix2162 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2162 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2162 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2162 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2162, value1032, value1074, value1079, value484, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2163 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2163 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound2163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2163 = Sparse.eval value2163 (momentVector H) := by
  have heq : pivotMatrix2163 = (fun u v => node2163 (pivotPermutation2163 u) v) := by apply Matrix.ext; unfold pivotMatrix2163 node2163 pivotPermutation2163; decide +kernel
  have hmoment : injectiveMoment H node2163 = injectiveMoment H pivotMatrix2163 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2163 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2163 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2163 (0 : Fin 4)) =
      Sparse.eval value1091 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2163 (0 : Fin 4) = raw4249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2163 raw4249; decide +kernel
    rw [heq]
    exact (canonical4249 hH).trans (sound1091 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2163 (1 : Fin 4)) =
      Sparse.eval value1104 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2163 (1 : Fin 4) = raw4300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2163 raw4300; decide +kernel
    rw [heq]
    exact (canonical4300 hH).trans (sound1104 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2163 (2 : Fin 4)) =
      Sparse.eval value673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2163 (2 : Fin 4) = raw4317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2163 raw4317; decide +kernel
    rw [heq]
    exact (canonical4317 hH).trans (sound673 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2163 (3 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2163 (3 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2163 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2163 + (injectiveMoment H (mergeFirst pivotMatrix2163 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2163 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2163 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2163 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2163, value1036, value1091, value1104, value673, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2164 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2164 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem sound2164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2164 = Sparse.eval value2164 (momentVector H) := by
  have heq : pivotMatrix2164 = (fun u v => node2164 (pivotPermutation2164 u) v) := by apply Matrix.ext; unfold pivotMatrix2164 node2164 pivotPermutation2164; decide +kernel
  have hmoment : injectiveMoment H node2164 = injectiveMoment H pivotMatrix2164 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2164 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2164 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2164 (0 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2164 (0 : Fin 4) = raw4250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2164 raw4250; decide +kernel
    rw [heq]
    exact (canonical4250 hH).trans (sound466 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2164 (1 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2164 (1 : Fin 4) = raw4301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2164 raw4301; decide +kernel
    rw [heq]
    exact (canonical4301 hH).trans (sound995 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2164 (2 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2164 (2 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2164 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2164 (3 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2164 (3 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2164 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2164 + (injectiveMoment H (mergeFirst pivotMatrix2164 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2164 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2164 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2164 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2164, value1036, value466, value502, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2165 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2165 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem sound2165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2165 = Sparse.eval value2165 (momentVector H) := by
  have heq : pivotMatrix2165 = (fun u v => node2165 (pivotPermutation2165 u) v) := by apply Matrix.ext; unfold pivotMatrix2165 node2165 pivotPermutation2165; decide +kernel
  have hmoment : injectiveMoment H node2165 = injectiveMoment H pivotMatrix2165 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2165 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2165 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2165 (0 : Fin 4)) =
      Sparse.eval value1309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2165 (0 : Fin 4) = raw4471 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2165 raw4471; decide +kernel
    rw [heq]
    exact (canonical4471 hH).trans (sound1309 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2165 (1 : Fin 4)) =
      Sparse.eval value1318 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2165 (1 : Fin 4) = raw4325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2165 raw4325; decide +kernel
    rw [heq]
    exact (canonical4325 hH).trans (sound1318 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2165 (2 : Fin 4)) =
      Sparse.eval value976 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2165 (2 : Fin 4) = raw4313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2165 raw4313; decide +kernel
    rw [heq]
    exact (canonical4313 hH).trans (sound976 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2165 (3 : Fin 4)) =
      Sparse.eval value1366 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2165 (3 : Fin 4) = raw4309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2165 raw4309; decide +kernel
    rw [heq]
    exact (canonical4309 hH).trans (sound1366 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2165 + (injectiveMoment H (mergeFirst pivotMatrix2165 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2165 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2165 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2165 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2165, value1309, value1318, value1366, value976, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2166 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2166 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound2166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2166 = Sparse.eval value2166 (momentVector H) := by
  have heq : pivotMatrix2166 = (fun u v => node2166 (pivotPermutation2166 u) v) := by apply Matrix.ext; unfold pivotMatrix2166 node2166 pivotPermutation2166; decide +kernel
  have hmoment : injectiveMoment H node2166 = injectiveMoment H pivotMatrix2166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2166 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2166 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2166 (0 : Fin 4)) =
      Sparse.eval value517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2166 (0 : Fin 4) = raw4475 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2166 raw4475; decide +kernel
    rw [heq]
    exact (canonical4475 hH).trans (sound517 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2166 (1 : Fin 4)) =
      Sparse.eval value674 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2166 (1 : Fin 4) = raw4328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2166 raw4328; decide +kernel
    rw [heq]
    exact (canonical4328 hH).trans (sound674 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2166 (2 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2166 (2 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2166 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2166 (3 : Fin 4)) =
      Sparse.eval value673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2166 (3 : Fin 4) = raw4317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2166 raw4317; decide +kernel
    rw [heq]
    exact (canonical4317 hH).trans (sound673 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2166 + (injectiveMoment H (mergeFirst pivotMatrix2166 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2166 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2166 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2166 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2166, value1036, value517, value673, value674, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2167 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2167 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2167 = Sparse.eval value2167 (momentVector H) := by
  have heq : pivotMatrix2167 = (fun u v => node2167 (pivotPermutation2167 u) v) := by apply Matrix.ext; unfold pivotMatrix2167 node2167 pivotPermutation2167; decide +kernel
  have hmoment : injectiveMoment H node2167 = injectiveMoment H pivotMatrix2167 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2167 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2167 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2167 (0 : Fin 4)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2167 (0 : Fin 4) = raw4476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2167 raw4476; decide +kernel
    rw [heq]
    exact (canonical4476 hH).trans (sound1078 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2167 (1 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2167 (1 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2167 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2167 (2 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2167 (2 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2167 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2167 (3 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2167 (3 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2167 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2167 + (injectiveMoment H (mergeFirst pivotMatrix2167 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2167 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2167 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2167 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2167, value1036, value1074, value1078, value502, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2168 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2168 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound2168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2168 = Sparse.eval value2168 (momentVector H) := by
  have heq : pivotMatrix2168 = (fun u v => node2168 (pivotPermutation2168 u) v) := by apply Matrix.ext; unfold pivotMatrix2168 node2168 pivotPermutation2168; decide +kernel
  have hmoment : injectiveMoment H node2168 = injectiveMoment H pivotMatrix2168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2168 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2168 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2168 (0 : Fin 4)) =
      Sparse.eval value993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2168 (0 : Fin 4) = raw5219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2168 raw5219; decide +kernel
    rw [heq]
    exact (canonical5219 hH).trans (sound993 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2168 (1 : Fin 4)) =
      Sparse.eval value1198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2168 (1 : Fin 4) = raw4384 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2168 raw4384; decide +kernel
    rw [heq]
    exact (canonical4384 hH).trans (sound1198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2168 (2 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2168 (2 : Fin 4) = raw4320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2168 raw4320; decide +kernel
    rw [heq]
    exact (canonical4320 hH).trans (sound1050 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2168 (3 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2168 (3 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2168 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2168 + (injectiveMoment H (mergeFirst pivotMatrix2168 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2168 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2168 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2168 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2168, value1036, value1050, value1198, value993, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2169 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2169 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound2169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2169 = Sparse.eval value2169 (momentVector H) := by
  have heq : pivotMatrix2169 = (fun u v => node2169 (pivotPermutation2169 u) v) := by apply Matrix.ext; unfold pivotMatrix2169 node2169 pivotPermutation2169; decide +kernel
  have hmoment : injectiveMoment H node2169 = injectiveMoment H pivotMatrix2169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2169 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2169 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2169 (0 : Fin 4)) =
      Sparse.eval value931 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2169 (0 : Fin 4) = raw5220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2169 raw5220; decide +kernel
    rw [heq]
    exact (canonical5220 hH).trans (sound931 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2169 (1 : Fin 4)) =
      Sparse.eval value964 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2169 (1 : Fin 4) = raw4385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2169 raw4385; decide +kernel
    rw [heq]
    exact (canonical4385 hH).trans (sound964 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2169 (2 : Fin 4)) =
      Sparse.eval value959 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2169 (2 : Fin 4) = raw4321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2169 raw4321; decide +kernel
    rw [heq]
    exact (canonical4321 hH).trans (sound959 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2169 (3 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2169 (3 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2169 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2169 + (injectiveMoment H (mergeFirst pivotMatrix2169 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2169 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2169 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2169 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2169, value502, value931, value959, value964, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2170 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2170 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem sound2170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2170 = Sparse.eval value2170 (momentVector H) := by
  have heq : pivotMatrix2170 = (fun u v => node2170 (pivotPermutation2170 u) v) := by apply Matrix.ext; unfold pivotMatrix2170 node2170 pivotPermutation2170; decide +kernel
  have hmoment : injectiveMoment H node2170 = injectiveMoment H pivotMatrix2170 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2170 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2170 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2170 (0 : Fin 4)) =
      Sparse.eval value500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2170 (0 : Fin 4) = raw5256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2170 raw5256; decide +kernel
    rw [heq]
    exact (canonical5256 hH).trans (sound500 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2170 (1 : Fin 4)) =
      Sparse.eval value1351 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2170 (1 : Fin 4) = raw4400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2170 raw4400; decide +kernel
    rw [heq]
    exact (canonical4400 hH).trans (sound1351 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2170 (2 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2170 (2 : Fin 4) = raw4320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2170 raw4320; decide +kernel
    rw [heq]
    exact (canonical4320 hH).trans (sound1050 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2170 (3 : Fin 4)) =
      Sparse.eval value673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2170 (3 : Fin 4) = raw4317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2170 raw4317; decide +kernel
    rw [heq]
    exact (canonical4317 hH).trans (sound673 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2170 + (injectiveMoment H (mergeFirst pivotMatrix2170 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2170 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2170 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2170 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2170, value1050, value1351, value500, value673, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2171 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2171 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound2171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2171 = Sparse.eval value2171 (momentVector H) := by
  have heq : pivotMatrix2171 = (fun u v => node2171 (pivotPermutation2171 u) v) := by apply Matrix.ext; unfold pivotMatrix2171 node2171 pivotPermutation2171; decide +kernel
  have hmoment : injectiveMoment H node2171 = injectiveMoment H pivotMatrix2171 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2171 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2171 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2171 (0 : Fin 4)) =
      Sparse.eval value1084 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2171 (0 : Fin 4) = raw5258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2171 raw5258; decide +kernel
    rw [heq]
    exact (canonical5258 hH).trans (sound1084 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2171 (1 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2171 (1 : Fin 4) = raw4402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2171 raw4402; decide +kernel
    rw [heq]
    exact (canonical4402 hH).trans (sound1083 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2171 (2 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2171 (2 : Fin 4) = raw4322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2171 raw4322; decide +kernel
    rw [heq]
    exact (canonical4322 hH).trans (sound1050 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2171 (3 : Fin 4)) =
      Sparse.eval value502 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2171 (3 : Fin 4) = raw4319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2171 raw4319; decide +kernel
    rw [heq]
    exact (canonical4319 hH).trans (sound502 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2171 + (injectiveMoment H (mergeFirst pivotMatrix2171 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2171 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2171 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2171 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2171, value1050, value1083, value1084, value502, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2172 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2172 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem sound2172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2172 = Sparse.eval value2172 (momentVector H) := by
  have heq : pivotMatrix2172 = (fun u v => node2172 (pivotPermutation2172 u) v) := by apply Matrix.ext; unfold pivotMatrix2172 node2172 pivotPermutation2172; decide +kernel
  have hmoment : injectiveMoment H node2172 = injectiveMoment H pivotMatrix2172 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2172 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2172 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2172 (0 : Fin 4)) =
      Sparse.eval value1333 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2172 (0 : Fin 4) = raw7813 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2172 raw7813; decide +kernel
    rw [heq]
    exact (canonical7813 hH).trans (sound1333 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2172 (1 : Fin 4)) =
      Sparse.eval value676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2172 (1 : Fin 4) = raw4437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2172 raw4437; decide +kernel
    rw [heq]
    exact (canonical4437 hH).trans (sound676 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2172 (2 : Fin 4)) =
      Sparse.eval value673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2172 (2 : Fin 4) = raw4323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2172 raw4323; decide +kernel
    rw [heq]
    exact (canonical4323 hH).trans (sound673 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2172 (3 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2172 (3 : Fin 4) = raw4316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2172 raw4316; decide +kernel
    rw [heq]
    exact (canonical4316 hH).trans (sound483 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2172 + (injectiveMoment H (mergeFirst pivotMatrix2172 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2172 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2172 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2172 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2172, value1333, value483, value673, value676, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2173 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2173 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem sound2173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2173 = Sparse.eval value2173 (momentVector H) := by
  have heq : pivotMatrix2173 = (fun u v => node2173 (pivotPermutation2173 u) v) := by apply Matrix.ext; unfold pivotMatrix2173 node2173 pivotPermutation2173; decide +kernel
  have hmoment : injectiveMoment H node2173 = injectiveMoment H pivotMatrix2173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2173 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2173 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2173 (0 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2173 (0 : Fin 4) = raw7082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2173 raw7082; decide +kernel
    rw [heq]
    exact (canonical7082 hH).trans (sound1207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2173 (1 : Fin 4)) =
      Sparse.eval value1248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2173 (1 : Fin 4) = raw4436 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2173 raw4436; decide +kernel
    rw [heq]
    exact (canonical4436 hH).trans (sound1248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2173 (2 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2173 (2 : Fin 4) = raw4322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2173 raw4322; decide +kernel
    rw [heq]
    exact (canonical4322 hH).trans (sound1050 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2173 (3 : Fin 4)) =
      Sparse.eval value483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2173 (3 : Fin 4) = raw4316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2173 raw4316; decide +kernel
    rw [heq]
    exact (canonical4316 hH).trans (sound483 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2173 + (injectiveMoment H (mergeFirst pivotMatrix2173 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2173 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2173 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2173 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2173, value1050, value1207, value1248, value483, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2174 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2174 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound2174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2174 = Sparse.eval value2174 (momentVector H) := by
  have heq : pivotMatrix2174 = (fun u v => node2174 (pivotPermutation2174 u) v) := by apply Matrix.ext; unfold pivotMatrix2174 node2174 pivotPermutation2174; decide +kernel
  have hmoment : injectiveMoment H node2174 = injectiveMoment H pivotMatrix2174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2174 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2174 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2174 (0 : Fin 4)) =
      Sparse.eval value1026 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2174 (0 : Fin 4) = raw4254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2174 raw4254; decide +kernel
    rw [heq]
    exact (canonical4254 hH).trans (sound1026 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2174 (1 : Fin 4)) =
      Sparse.eval value1036 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2174 (1 : Fin 4) = raw4318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2174 raw4318; decide +kernel
    rw [heq]
    exact (canonical4318 hH).trans (sound1036 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2174 (2 : Fin 4)) =
      Sparse.eval value674 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2174 (2 : Fin 4) = raw4328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2174 raw4328; decide +kernel
    rw [heq]
    exact (canonical4328 hH).trans (sound674 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2174 (3 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2174 (3 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2174 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2174 + (injectiveMoment H (mergeFirst pivotMatrix2174 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2174 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2174 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2174 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2174, value1026, value1036, value1074, value674, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2175 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2175 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound2175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2175 = Sparse.eval value2175 (momentVector H) := by
  have heq : pivotMatrix2175 = (fun u v => node2175 (pivotPermutation2175 u) v) := by apply Matrix.ext; unfold pivotMatrix2175 node2175 pivotPermutation2175; decide +kernel
  have hmoment : injectiveMoment H node2175 = injectiveMoment H pivotMatrix2175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2175 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2175 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2175 (0 : Fin 4)) =
      Sparse.eval value1024 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2175 (0 : Fin 4) = raw5221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2175 raw5221; decide +kernel
    rw [heq]
    exact (canonical5221 hH).trans (sound1024 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2175 (1 : Fin 4)) =
      Sparse.eval value1032 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2175 (1 : Fin 4) = raw4401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2175 raw4401; decide +kernel
    rw [heq]
    exact (canonical4401 hH).trans (sound1032 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2175 (2 : Fin 4)) =
      Sparse.eval value1046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2175 (2 : Fin 4) = raw4330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2175 raw4330; decide +kernel
    rw [heq]
    exact (canonical4330 hH).trans (sound1046 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2175 (3 : Fin 4)) =
      Sparse.eval value1074 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2175 (3 : Fin 4) = raw4329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2175 raw4329; decide +kernel
    rw [heq]
    exact (canonical4329 hH).trans (sound1074 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2175 + (injectiveMoment H (mergeFirst pivotMatrix2175 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2175 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2175 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2175 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2175, value1024, value1032, value1046, value1074, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
