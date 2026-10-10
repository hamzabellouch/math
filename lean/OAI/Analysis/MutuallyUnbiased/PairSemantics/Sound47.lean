import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical57
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical71
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical116

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation3008 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3008 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound3008 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3008 = Sparse.eval value3008 (momentVector H) := by
  have heq : pivotMatrix3008 = (fun u v => node3008 (pivotPermutation3008 u) v) := by apply Matrix.ext; unfold pivotMatrix3008 node3008 pivotPermutation3008; decide +kernel
  have hmoment : injectiveMoment H node3008 = injectiveMoment H pivotMatrix3008 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3008 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3008 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3008 (0 : Fin 5)) =
      Sparse.eval value1819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3008 (0 : Fin 5) = raw2395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3008 raw2395; decide +kernel
    rw [heq]
    exact (canonical2395 hH).trans (sound1819 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3008 (1 : Fin 5)) =
      Sparse.eval value2627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3008 (1 : Fin 5) = raw2026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3008 raw2026; decide +kernel
    rw [heq]
    exact (canonical2026 hH).trans (sound2627 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3008 (2 : Fin 5)) =
      Sparse.eval value1711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3008 (2 : Fin 5) = raw1991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3008 raw1991; decide +kernel
    rw [heq]
    exact (canonical1991 hH).trans (sound1711 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3008 (3 : Fin 5)) =
      Sparse.eval value1710 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3008 (3 : Fin 5) = raw1989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3008 raw1989; decide +kernel
    rw [heq]
    exact (canonical1989 hH).trans (sound1710 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3008 (4 : Fin 5)) =
      Sparse.eval value1709 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3008 (4 : Fin 5) = raw1988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3008 raw1988; decide +kernel
    rw [heq]
    exact (canonical1988 hH).trans (sound1709 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3008 + (injectiveMoment H (mergeFirst pivotMatrix3008 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3008 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3008 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3008 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3008 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3008, value1709, value1710, value1711, value1819, value2627, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3009 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3009 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3009 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3009 = Sparse.eval value3009 (momentVector H) := by
  have heq : pivotMatrix3009 = (fun u v => node3009 (pivotPermutation3009 u) v) := by apply Matrix.ext; unfold pivotMatrix3009 node3009 pivotPermutation3009; decide +kernel
  have hmoment : injectiveMoment H node3009 = injectiveMoment H pivotMatrix3009 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3009 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3009 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3009 (0 : Fin 5)) =
      Sparse.eval value1821 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3009 (0 : Fin 5) = raw2400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3009 raw2400; decide +kernel
    rw [heq]
    exact (canonical2400 hH).trans (sound1821 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3009 (1 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3009 (1 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3009 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3009 (2 : Fin 5)) =
      Sparse.eval value1713 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3009 (2 : Fin 5) = raw1996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3009 raw1996; decide +kernel
    rw [heq]
    exact (canonical1996 hH).trans (sound1713 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3009 (3 : Fin 5)) =
      Sparse.eval value1712 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3009 (3 : Fin 5) = raw1994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3009 raw1994; decide +kernel
    rw [heq]
    exact (canonical1994 hH).trans (sound1712 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3009 (4 : Fin 5)) =
      Sparse.eval value1668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3009 (4 : Fin 5) = raw1993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3009 raw1993; decide +kernel
    rw [heq]
    exact (canonical1993 hH).trans (sound1668 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3009 + (injectiveMoment H (mergeFirst pivotMatrix3009 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3009 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3009 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3009 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3009 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3009, value1668, value1712, value1713, value1720, value1821, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3010 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3010 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem sound3010 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3010 = Sparse.eval value3010 (momentVector H) := by
  have heq : pivotMatrix3010 = (fun u v => node3010 (pivotPermutation3010 u) v) := by apply Matrix.ext; unfold pivotMatrix3010 node3010 pivotPermutation3010; decide +kernel
  have hmoment : injectiveMoment H node3010 = injectiveMoment H pivotMatrix3010 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3010 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3010 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3010 (0 : Fin 5)) =
      Sparse.eval value1822 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3010 (0 : Fin 5) = raw2415 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3010 raw2415; decide +kernel
    rw [heq]
    exact (canonical2415 hH).trans (sound1822 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3010 (1 : Fin 5)) =
      Sparse.eval value1671 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3010 (1 : Fin 5) = raw2054 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3010 raw2054; decide +kernel
    rw [heq]
    exact (canonical2054 hH).trans (sound1671 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3010 (2 : Fin 5)) =
      Sparse.eval value1671 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3010 (2 : Fin 5) = raw2024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3010 raw2024; decide +kernel
    rw [heq]
    exact (canonical2024 hH).trans (sound1671 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3010 (3 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3010 (3 : Fin 5) = raw2017 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3010 raw2017; decide +kernel
    rw [heq]
    exact (canonical2017 hH).trans (sound1644 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3010 (4 : Fin 5)) =
      Sparse.eval value1714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3010 (4 : Fin 5) = raw2016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3010 raw2016; decide +kernel
    rw [heq]
    exact (canonical2016 hH).trans (sound1714 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3010 + (injectiveMoment H (mergeFirst pivotMatrix3010 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3010 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3010 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3010 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3010 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3010, value1644, value1671, value1714, value1822, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3011 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3011 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound3011 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3011 = Sparse.eval value3011 (momentVector H) := by
  have heq : pivotMatrix3011 = (fun u v => node3011 (pivotPermutation3011 u) v) := by apply Matrix.ext; unfold pivotMatrix3011 node3011 pivotPermutation3011; decide +kernel
  have hmoment : injectiveMoment H node3011 = injectiveMoment H pivotMatrix3011 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3011 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3011 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3011 (0 : Fin 5)) =
      Sparse.eval value1785 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3011 (0 : Fin 5) = raw2416 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3011 raw2416; decide +kernel
    rw [heq]
    exact (canonical2416 hH).trans (sound1785 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3011 (1 : Fin 5)) =
      Sparse.eval value2580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3011 (1 : Fin 5) = raw2055 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3011 raw2055; decide +kernel
    rw [heq]
    exact (canonical2055 hH).trans (sound2580 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3011 (2 : Fin 5)) =
      Sparse.eval value2580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3011 (2 : Fin 5) = raw2025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3011 raw2025; decide +kernel
    rw [heq]
    exact (canonical2025 hH).trans (sound2580 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3011 (3 : Fin 5)) =
      Sparse.eval value1715 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3011 (3 : Fin 5) = raw2018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3011 raw2018; decide +kernel
    rw [heq]
    exact (canonical2018 hH).trans (sound1715 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3011 (4 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3011 (4 : Fin 5) = raw2017 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3011 raw2017; decide +kernel
    rw [heq]
    exact (canonical2017 hH).trans (sound1644 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3011 + (injectiveMoment H (mergeFirst pivotMatrix3011 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3011 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3011 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3011 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3011 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3011, value1644, value1715, value1785, value2580, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3012 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3012 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound3012 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3012 = Sparse.eval value3012 (momentVector H) := by
  have heq : pivotMatrix3012 = (fun u v => node3012 (pivotPermutation3012 u) v) := by apply Matrix.ext; unfold pivotMatrix3012 node3012 pivotPermutation3012; decide +kernel
  have hmoment : injectiveMoment H node3012 = injectiveMoment H pivotMatrix3012 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3012 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3012 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3012 (0 : Fin 5)) =
      Sparse.eval value1823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3012 (0 : Fin 5) = raw2417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3012 raw2417; decide +kernel
    rw [heq]
    exact (canonical2417 hH).trans (sound1823 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3012 (1 : Fin 5)) =
      Sparse.eval value2627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3012 (1 : Fin 5) = raw2056 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3012 raw2056; decide +kernel
    rw [heq]
    exact (canonical2056 hH).trans (sound2627 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3012 (2 : Fin 5)) =
      Sparse.eval value2627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3012 (2 : Fin 5) = raw2026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3012 raw2026; decide +kernel
    rw [heq]
    exact (canonical2026 hH).trans (sound2627 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3012 (3 : Fin 5)) =
      Sparse.eval value1716 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3012 (3 : Fin 5) = raw2019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3012 raw2019; decide +kernel
    rw [heq]
    exact (canonical2019 hH).trans (sound1716 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3012 (4 : Fin 5)) =
      Sparse.eval value1715 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3012 (4 : Fin 5) = raw2018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3012 raw2018; decide +kernel
    rw [heq]
    exact (canonical2018 hH).trans (sound1715 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3012 + (injectiveMoment H (mergeFirst pivotMatrix3012 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3012 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3012 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3012 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3012 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3012, value1715, value1716, value1823, value2627, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3013 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3013 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem sound3013 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3013 = Sparse.eval value3013 (momentVector H) := by
  have heq : pivotMatrix3013 = (fun u v => node3013 (pivotPermutation3013 u) v) := by apply Matrix.ext; unfold pivotMatrix3013 node3013 pivotPermutation3013; decide +kernel
  have hmoment : injectiveMoment H node3013 = injectiveMoment H pivotMatrix3013 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3013 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3013 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3013 (0 : Fin 5)) =
      Sparse.eval value1825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3013 (0 : Fin 5) = raw2422 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3013 raw2422; decide +kernel
    rw [heq]
    exact (canonical2422 hH).trans (sound1825 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3013 (1 : Fin 5)) =
      Sparse.eval value2640 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3013 (1 : Fin 5) = raw2059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3013 raw2059; decide +kernel
    rw [heq]
    exact (canonical2059 hH).trans (sound2640 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3013 (2 : Fin 5)) =
      Sparse.eval value1719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3013 (2 : Fin 5) = raw2031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3013 raw2031; decide +kernel
    rw [heq]
    exact (canonical2031 hH).trans (sound1719 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3013 (3 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3013 (3 : Fin 5) = raw2027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3013 raw2027; decide +kernel
    rw [heq]
    exact (canonical2027 hH).trans (sound1718 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3013 (4 : Fin 5)) =
      Sparse.eval value2627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3013 (4 : Fin 5) = raw2026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3013 raw2026; decide +kernel
    rw [heq]
    exact (canonical2026 hH).trans (sound2627 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3013 + (injectiveMoment H (mergeFirst pivotMatrix3013 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3013 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3013 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3013 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3013 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3013, value1718, value1719, value1825, value2627, value2640, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3014 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3014 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3014 = Sparse.eval value3014 (momentVector H) := by
  have heq : pivotMatrix3014 = (fun u v => node3014 (pivotPermutation3014 u) v) := by apply Matrix.ext; unfold pivotMatrix3014 node3014 pivotPermutation3014; decide +kernel
  have hmoment : injectiveMoment H node3014 = injectiveMoment H pivotMatrix3014 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3014 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3014 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3014 (0 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3014 (0 : Fin 5) = raw2426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3014 raw2426; decide +kernel
    rw [heq]
    exact (canonical2426 hH).trans (sound1786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3014 (1 : Fin 5)) =
      Sparse.eval value2579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3014 (1 : Fin 5) = raw2061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3014 raw2061; decide +kernel
    rw [heq]
    exact (canonical2061 hH).trans (sound2579 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3014 (2 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3014 (2 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3014 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3014 (3 : Fin 5)) =
      Sparse.eval value1719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3014 (3 : Fin 5) = raw2031 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3014 raw2031; decide +kernel
    rw [heq]
    exact (canonical2031 hH).trans (sound1719 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3014 (4 : Fin 5)) =
      Sparse.eval value2605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3014 (4 : Fin 5) = raw2030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3014 raw2030; decide +kernel
    rw [heq]
    exact (canonical2030 hH).trans (sound2605 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3014 + (injectiveMoment H (mergeFirst pivotMatrix3014 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3014 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3014 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3014 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3014 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3014, value1719, value1720, value1786, value2579, value2605, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3015 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3015 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound3015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3015 = Sparse.eval value3015 (momentVector H) := by
  have heq : pivotMatrix3015 = (fun u v => node3015 (pivotPermutation3015 u) v) := by apply Matrix.ext; unfold pivotMatrix3015 node3015 pivotPermutation3015; decide +kernel
  have hmoment : injectiveMoment H node3015 = injectiveMoment H pivotMatrix3015 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3015 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3015 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3015 (0 : Fin 5)) =
      Sparse.eval value1827 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3015 (0 : Fin 5) = raw2429 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3015 raw2429; decide +kernel
    rw [heq]
    exact (canonical2429 hH).trans (sound1827 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3015 (1 : Fin 5)) =
      Sparse.eval value1625 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3015 (1 : Fin 5) = raw2064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3015 raw2064; decide +kernel
    rw [heq]
    exact (canonical2064 hH).trans (sound1625 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3015 (2 : Fin 5)) =
      Sparse.eval value1722 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3015 (2 : Fin 5) = raw2039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3015 raw2039; decide +kernel
    rw [heq]
    exact (canonical2039 hH).trans (sound1722 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3015 (3 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3015 (3 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3015 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3015 (4 : Fin 5)) =
      Sparse.eval value1669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3015 (4 : Fin 5) = raw2034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3015 raw2034; decide +kernel
    rw [heq]
    exact (canonical2034 hH).trans (sound1669 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3015 + (injectiveMoment H (mergeFirst pivotMatrix3015 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3015 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3015 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3015 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3015 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3015, value1625, value1669, value1720, value1722, value1827, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3016 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3016 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound3016 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3016 = Sparse.eval value3016 (momentVector H) := by
  have heq : pivotMatrix3016 = (fun u v => node3016 (pivotPermutation3016 u) v) := by apply Matrix.ext; unfold pivotMatrix3016 node3016 pivotPermutation3016; decide +kernel
  have hmoment : injectiveMoment H node3016 = injectiveMoment H pivotMatrix3016 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3016 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3016 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3016 (0 : Fin 5)) =
      Sparse.eval value1828 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3016 (0 : Fin 5) = raw2430 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3016 raw2430; decide +kernel
    rw [heq]
    exact (canonical2430 hH).trans (sound1828 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3016 (1 : Fin 5)) =
      Sparse.eval value1623 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3016 (1 : Fin 5) = raw2065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3016 raw2065; decide +kernel
    rw [heq]
    exact (canonical2065 hH).trans (sound1623 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3016 (2 : Fin 5)) =
      Sparse.eval value1723 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3016 (2 : Fin 5) = raw2040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3016 raw2040; decide +kernel
    rw [heq]
    exact (canonical2040 hH).trans (sound1723 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3016 (3 : Fin 5)) =
      Sparse.eval value1721 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3016 (3 : Fin 5) = raw2036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3016 raw2036; decide +kernel
    rw [heq]
    exact (canonical2036 hH).trans (sound1721 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3016 (4 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3016 (4 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3016 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3016 + (injectiveMoment H (mergeFirst pivotMatrix3016 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3016 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3016 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3016 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3016 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3016, value1623, value1720, value1721, value1723, value1828, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3017 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3017 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound3017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3017 = Sparse.eval value3017 (momentVector H) := by
  have heq : pivotMatrix3017 = (fun u v => node3017 (pivotPermutation3017 u) v) := by apply Matrix.ext; unfold pivotMatrix3017 node3017 pivotPermutation3017; decide +kernel
  have hmoment : injectiveMoment H node3017 = injectiveMoment H pivotMatrix3017 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3017 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3017 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3017 (0 : Fin 5)) =
      Sparse.eval value2810 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3017 (0 : Fin 5) = raw3140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3017 raw3140; decide +kernel
    rw [heq]
    exact (canonical3140 hH).trans (sound2810 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3017 (1 : Fin 5)) =
      Sparse.eval value2605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3017 (1 : Fin 5) = raw2075 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3017 raw2075; decide +kernel
    rw [heq]
    exact (canonical2075 hH).trans (sound2605 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3017 (2 : Fin 5)) =
      Sparse.eval value1702 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3017 (2 : Fin 5) = raw1966 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3017 raw1966; decide +kernel
    rw [heq]
    exact (canonical1966 hH).trans (sound1702 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3017 (3 : Fin 5)) =
      Sparse.eval value2428 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3017 (3 : Fin 5) = raw1956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3017 raw1956; decide +kernel
    rw [heq]
    exact (canonical1956 hH).trans (sound2428 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3017 (4 : Fin 5)) =
      Sparse.eval value1698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3017 (4 : Fin 5) = raw1955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3017 raw1955; decide +kernel
    rw [heq]
    exact (canonical1955 hH).trans (sound1698 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3017 + (injectiveMoment H (mergeFirst pivotMatrix3017 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3017 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3017 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3017 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3017 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3017, value1698, value1702, value2428, value2605, value2810, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3018 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3018 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3018 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3018 = Sparse.eval value3018 (momentVector H) := by
  have heq : pivotMatrix3018 = (fun u v => node3018 (pivotPermutation3018 u) v) := by apply Matrix.ext; unfold pivotMatrix3018 node3018 pivotPermutation3018; decide +kernel
  have hmoment : injectiveMoment H node3018 = injectiveMoment H pivotMatrix3018 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3018 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3018 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3018 (0 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3018 (0 : Fin 5) = raw3145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3018 raw3145; decide +kernel
    rw [heq]
    exact (canonical3145 hH).trans (sound2740 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3018 (1 : Fin 5)) =
      Sparse.eval value2579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3018 (1 : Fin 5) = raw2077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3018 raw2077; decide +kernel
    rw [heq]
    exact (canonical2077 hH).trans (sound2579 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3018 (2 : Fin 5)) =
      Sparse.eval value1704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3018 (2 : Fin 5) = raw1969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3018 raw1969; decide +kernel
    rw [heq]
    exact (canonical1969 hH).trans (sound1704 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3018 (3 : Fin 5)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3018 (3 : Fin 5) = raw1963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3018 raw1963; decide +kernel
    rw [heq]
    exact (canonical1963 hH).trans (sound2427 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3018 (4 : Fin 5)) =
      Sparse.eval value1701 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3018 (4 : Fin 5) = raw1961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3018 raw1961; decide +kernel
    rw [heq]
    exact (canonical1961 hH).trans (sound1701 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3018 + (injectiveMoment H (mergeFirst pivotMatrix3018 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3018 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3018 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3018 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3018 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3018, value1701, value1704, value2427, value2579, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3019 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3019 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem sound3019 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3019 = Sparse.eval value3019 (momentVector H) := by
  have heq : pivotMatrix3019 = (fun u v => node3019 (pivotPermutation3019 u) v) := by apply Matrix.ext; unfold pivotMatrix3019 node3019 pivotPermutation3019; decide +kernel
  have hmoment : injectiveMoment H node3019 = injectiveMoment H pivotMatrix3019 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3019 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3019 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3019 (0 : Fin 5)) =
      Sparse.eval value1494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3019 (0 : Fin 5) = raw1181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3019 raw1181; decide +kernel
    rw [heq]
    exact (canonical1181 hH).trans (sound1494 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3019 (1 : Fin 5)) =
      Sparse.eval value1725 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3019 (1 : Fin 5) = raw2154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3019 raw2154; decide +kernel
    rw [heq]
    exact (canonical2154 hH).trans (sound1725 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3019 (2 : Fin 5)) =
      Sparse.eval value2437 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3019 (2 : Fin 5) = raw2236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3019 raw2236; decide +kernel
    rw [heq]
    exact (canonical2236 hH).trans (sound2437 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3019 (3 : Fin 5)) =
      Sparse.eval value2437 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3019 (3 : Fin 5) = raw2247 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3019 raw2247; decide +kernel
    rw [heq]
    exact (canonical2247 hH).trans (sound2437 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3019 (4 : Fin 5)) =
      Sparse.eval value1765 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3019 (4 : Fin 5) = raw2249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3019 raw2249; decide +kernel
    rw [heq]
    exact (canonical2249 hH).trans (sound1765 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3019 + (injectiveMoment H (mergeFirst pivotMatrix3019 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3019 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3019 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3019 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3019 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3019, value1494, value1725, value1765, value2437, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3020 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3020 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound3020 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3020 = Sparse.eval value3020 (momentVector H) := by
  have heq : pivotMatrix3020 = (fun u v => node3020 (pivotPermutation3020 u) v) := by apply Matrix.ext; unfold pivotMatrix3020 node3020 pivotPermutation3020; decide +kernel
  have hmoment : injectiveMoment H node3020 = injectiveMoment H pivotMatrix3020 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3020 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3020 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3020 (0 : Fin 5)) =
      Sparse.eval value1496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3020 (0 : Fin 5) = raw1182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3020 raw1182; decide +kernel
    rw [heq]
    exact (canonical1182 hH).trans (sound1496 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3020 (1 : Fin 5)) =
      Sparse.eval value1726 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3020 (1 : Fin 5) = raw2155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3020 raw2155; decide +kernel
    rw [heq]
    exact (canonical2155 hH).trans (sound1726 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3020 (2 : Fin 5)) =
      Sparse.eval value2435 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3020 (2 : Fin 5) = raw2237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3020 raw2237; decide +kernel
    rw [heq]
    exact (canonical2237 hH).trans (sound2435 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3020 (3 : Fin 5)) =
      Sparse.eval value2440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3020 (3 : Fin 5) = raw2248 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3020 raw2248; decide +kernel
    rw [heq]
    exact (canonical2248 hH).trans (sound2440 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3020 (4 : Fin 5)) =
      Sparse.eval value1766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3020 (4 : Fin 5) = raw2250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3020 raw2250; decide +kernel
    rw [heq]
    exact (canonical2250 hH).trans (sound1766 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3020 + (injectiveMoment H (mergeFirst pivotMatrix3020 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3020 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3020 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3020 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3020 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3020, value1496, value1726, value1766, value2435, value2440, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3021 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3021 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound3021 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3021 = Sparse.eval value3021 (momentVector H) := by
  have heq : pivotMatrix3021 = (fun u v => node3021 (pivotPermutation3021 u) v) := by apply Matrix.ext; unfold pivotMatrix3021 node3021 pivotPermutation3021; decide +kernel
  have hmoment : injectiveMoment H node3021 = injectiveMoment H pivotMatrix3021 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3021 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3021 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3021 (0 : Fin 5)) =
      Sparse.eval value1497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3021 (0 : Fin 5) = raw1183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3021 raw1183; decide +kernel
    rw [heq]
    exact (canonical1183 hH).trans (sound1497 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3021 (1 : Fin 5)) =
      Sparse.eval value1727 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3021 (1 : Fin 5) = raw2156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3021 raw2156; decide +kernel
    rw [heq]
    exact (canonical2156 hH).trans (sound1727 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3021 (2 : Fin 5)) =
      Sparse.eval value2433 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3021 (2 : Fin 5) = raw2239 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3021 raw2239; decide +kernel
    rw [heq]
    exact (canonical2239 hH).trans (sound2433 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3021 (3 : Fin 5)) =
      Sparse.eval value1767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3021 (3 : Fin 5) = raw2251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3021 raw2251; decide +kernel
    rw [heq]
    exact (canonical2251 hH).trans (sound1767 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3021 (4 : Fin 5)) =
      Sparse.eval value2444 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3021 (4 : Fin 5) = raw2253 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3021 raw2253; decide +kernel
    rw [heq]
    exact (canonical2253 hH).trans (sound2444 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3021 + (injectiveMoment H (mergeFirst pivotMatrix3021 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3021 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3021 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3021 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3021 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3021, value1497, value1727, value1767, value2433, value2444, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3022 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3022 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem sound3022 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3022 = Sparse.eval value3022 (momentVector H) := by
  have heq : pivotMatrix3022 = (fun u v => node3022 (pivotPermutation3022 u) v) := by apply Matrix.ext; unfold pivotMatrix3022 node3022 pivotPermutation3022; decide +kernel
  have hmoment : injectiveMoment H node3022 = injectiveMoment H pivotMatrix3022 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3022 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3022 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3022 (0 : Fin 5)) =
      Sparse.eval value1498 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3022 (0 : Fin 5) = raw1184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3022 raw1184; decide +kernel
    rw [heq]
    exact (canonical1184 hH).trans (sound1498 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3022 (1 : Fin 5)) =
      Sparse.eval value1728 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3022 (1 : Fin 5) = raw2157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3022 raw2157; decide +kernel
    rw [heq]
    exact (canonical2157 hH).trans (sound1728 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3022 (2 : Fin 5)) =
      Sparse.eval value2434 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3022 (2 : Fin 5) = raw2240 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3022 raw2240; decide +kernel
    rw [heq]
    exact (canonical2240 hH).trans (sound2434 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3022 (3 : Fin 5)) =
      Sparse.eval value1768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3022 (3 : Fin 5) = raw2252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3022 raw2252; decide +kernel
    rw [heq]
    exact (canonical2252 hH).trans (sound1768 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3022 (4 : Fin 5)) =
      Sparse.eval value2445 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3022 (4 : Fin 5) = raw2254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3022 raw2254; decide +kernel
    rw [heq]
    exact (canonical2254 hH).trans (sound2445 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3022 + (injectiveMoment H (mergeFirst pivotMatrix3022 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3022 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3022 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3022 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3022 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3022, value1498, value1728, value1768, value2434, value2445, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3023 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3023 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound3023 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3023 = Sparse.eval value3023 (momentVector H) := by
  have heq : pivotMatrix3023 = (fun u v => node3023 (pivotPermutation3023 u) v) := by apply Matrix.ext; unfold pivotMatrix3023 node3023 pivotPermutation3023; decide +kernel
  have hmoment : injectiveMoment H node3023 = injectiveMoment H pivotMatrix3023 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3023 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3023 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3023 (0 : Fin 5)) =
      Sparse.eval value1499 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3023 (0 : Fin 5) = raw1186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3023 raw1186; decide +kernel
    rw [heq]
    exact (canonical1186 hH).trans (sound1499 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3023 (1 : Fin 5)) =
      Sparse.eval value1729 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3023 (1 : Fin 5) = raw2159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3023 raw2159; decide +kernel
    rw [heq]
    exact (canonical2159 hH).trans (sound1729 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3023 (2 : Fin 5)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3023 (2 : Fin 5) = raw2241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3023 raw2241; decide +kernel
    rw [heq]
    exact (canonical2241 hH).trans (sound837 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3023 (3 : Fin 5)) =
      Sparse.eval value2439 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3023 (3 : Fin 5) = raw2255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3023 raw2255; decide +kernel
    rw [heq]
    exact (canonical2255 hH).trans (sound2439 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3023 (4 : Fin 5)) =
      Sparse.eval value1769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3023 (4 : Fin 5) = raw2257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3023 raw2257; decide +kernel
    rw [heq]
    exact (canonical2257 hH).trans (sound1769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3023 + (injectiveMoment H (mergeFirst pivotMatrix3023 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3023 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3023 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3023 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3023 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3023, value1499, value1729, value1769, value2439, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3024 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3024 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound3024 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3024 = Sparse.eval value3024 (momentVector H) := by
  have heq : pivotMatrix3024 = (fun u v => node3024 (pivotPermutation3024 u) v) := by apply Matrix.ext; unfold pivotMatrix3024 node3024 pivotPermutation3024; decide +kernel
  have hmoment : injectiveMoment H node3024 = injectiveMoment H pivotMatrix3024 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3024 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3024 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3024 (0 : Fin 5)) =
      Sparse.eval value1498 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3024 (0 : Fin 5) = raw1187 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3024 raw1187; decide +kernel
    rw [heq]
    exact (canonical1187 hH).trans (sound1498 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3024 (1 : Fin 5)) =
      Sparse.eval value1730 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3024 (1 : Fin 5) = raw2160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3024 raw2160; decide +kernel
    rw [heq]
    exact (canonical2160 hH).trans (sound1730 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3024 (2 : Fin 5)) =
      Sparse.eval value1116 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3024 (2 : Fin 5) = raw2242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3024 raw2242; decide +kernel
    rw [heq]
    exact (canonical2242 hH).trans (sound1116 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3024 (3 : Fin 5)) =
      Sparse.eval value1770 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3024 (3 : Fin 5) = raw2258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3024 raw2258; decide +kernel
    rw [heq]
    exact (canonical2258 hH).trans (sound1770 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3024 (4 : Fin 5)) =
      Sparse.eval value2443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3024 (4 : Fin 5) = raw2260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3024 raw2260; decide +kernel
    rw [heq]
    exact (canonical2260 hH).trans (sound2443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3024 + (injectiveMoment H (mergeFirst pivotMatrix3024 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3024 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3024 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3024 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3024 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3024, value1116, value1498, value1730, value1770, value2443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3025 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3025 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound3025 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3025 = Sparse.eval value3025 (momentVector H) := by
  have heq : pivotMatrix3025 = (fun u v => node3025 (pivotPermutation3025 u) v) := by apply Matrix.ext; unfold pivotMatrix3025 node3025 pivotPermutation3025; decide +kernel
  have hmoment : injectiveMoment H node3025 = injectiveMoment H pivotMatrix3025 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3025 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3025 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3025 (0 : Fin 5)) =
      Sparse.eval value1500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3025 (0 : Fin 5) = raw1188 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3025 raw1188; decide +kernel
    rw [heq]
    exact (canonical1188 hH).trans (sound1500 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3025 (1 : Fin 5)) =
      Sparse.eval value1731 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3025 (1 : Fin 5) = raw2161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3025 raw2161; decide +kernel
    rw [heq]
    exact (canonical2161 hH).trans (sound1731 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3025 (2 : Fin 5)) =
      Sparse.eval value835 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3025 (2 : Fin 5) = raw2243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3025 raw2243; decide +kernel
    rw [heq]
    exact (canonical2243 hH).trans (sound835 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3025 (3 : Fin 5)) =
      Sparse.eval value1771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3025 (3 : Fin 5) = raw2259 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3025 raw2259; decide +kernel
    rw [heq]
    exact (canonical2259 hH).trans (sound1771 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3025 (4 : Fin 5)) =
      Sparse.eval value2443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3025 (4 : Fin 5) = raw2262 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3025 raw2262; decide +kernel
    rw [heq]
    exact (canonical2262 hH).trans (sound2443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3025 + (injectiveMoment H (mergeFirst pivotMatrix3025 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3025 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3025 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3025 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3025 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3025, value1500, value1731, value1771, value2443, value835, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3026 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3026 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound3026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3026 = Sparse.eval value3026 (momentVector H) := by
  have heq : pivotMatrix3026 = (fun u v => node3026 (pivotPermutation3026 u) v) := by apply Matrix.ext; unfold pivotMatrix3026 node3026 pivotPermutation3026; decide +kernel
  have hmoment : injectiveMoment H node3026 = injectiveMoment H pivotMatrix3026 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3026 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3026 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3026 (0 : Fin 5)) =
      Sparse.eval value1500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3026 (0 : Fin 5) = raw1190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3026 raw1190; decide +kernel
    rw [heq]
    exact (canonical1190 hH).trans (sound1500 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3026 (1 : Fin 5)) =
      Sparse.eval value1732 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3026 (1 : Fin 5) = raw2162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3026 raw2162; decide +kernel
    rw [heq]
    exact (canonical2162 hH).trans (sound1732 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3026 (2 : Fin 5)) =
      Sparse.eval value2438 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3026 (2 : Fin 5) = raw2245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3026 raw2245; decide +kernel
    rw [heq]
    exact (canonical2245 hH).trans (sound2438 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3026 (3 : Fin 5)) =
      Sparse.eval value1772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3026 (3 : Fin 5) = raw2264 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3026 raw2264; decide +kernel
    rw [heq]
    exact (canonical2264 hH).trans (sound1772 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3026 (4 : Fin 5)) =
      Sparse.eval value2442 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3026 (4 : Fin 5) = raw2266 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3026 raw2266; decide +kernel
    rw [heq]
    exact (canonical2266 hH).trans (sound2442 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3026 + (injectiveMoment H (mergeFirst pivotMatrix3026 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3026 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3026 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3026 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3026 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3026, value1500, value1732, value1772, value2438, value2442, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3027 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3027 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound3027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3027 = Sparse.eval value3027 (momentVector H) := by
  have heq : pivotMatrix3027 = (fun u v => node3027 (pivotPermutation3027 u) v) := by apply Matrix.ext; unfold pivotMatrix3027 node3027 pivotPermutation3027; decide +kernel
  have hmoment : injectiveMoment H node3027 = injectiveMoment H pivotMatrix3027 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3027 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3027 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3027 (0 : Fin 5)) =
      Sparse.eval value1499 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3027 (0 : Fin 5) = raw1192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3027 raw1192; decide +kernel
    rw [heq]
    exact (canonical1192 hH).trans (sound1499 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3027 (1 : Fin 5)) =
      Sparse.eval value1733 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3027 (1 : Fin 5) = raw2165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3027 raw2165; decide +kernel
    rw [heq]
    exact (canonical2165 hH).trans (sound1733 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3027 (2 : Fin 5)) =
      Sparse.eval value2445 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3027 (2 : Fin 5) = raw2254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3027 raw2254; decide +kernel
    rw [heq]
    exact (canonical2254 hH).trans (sound2445 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3027 (3 : Fin 5)) =
      Sparse.eval value1773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3027 (3 : Fin 5) = raw2269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3027 raw2269; decide +kernel
    rw [heq]
    exact (canonical2269 hH).trans (sound1773 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3027 (4 : Fin 5)) =
      Sparse.eval value1774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3027 (4 : Fin 5) = raw2271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3027 raw2271; decide +kernel
    rw [heq]
    exact (canonical2271 hH).trans (sound1774 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3027 + (injectiveMoment H (mergeFirst pivotMatrix3027 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3027 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3027 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3027 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3027 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3027, value1499, value1733, value1773, value1774, value2445, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3028 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3028 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound3028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3028 = Sparse.eval value3028 (momentVector H) := by
  have heq : pivotMatrix3028 = (fun u v => node3028 (pivotPermutation3028 u) v) := by apply Matrix.ext; unfold pivotMatrix3028 node3028 pivotPermutation3028; decide +kernel
  have hmoment : injectiveMoment H node3028 = injectiveMoment H pivotMatrix3028 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3028 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3028 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3028 (0 : Fin 5)) =
      Sparse.eval value1496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3028 (0 : Fin 5) = raw1194 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3028 raw1194; decide +kernel
    rw [heq]
    exact (canonical1194 hH).trans (sound1496 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3028 (1 : Fin 5)) =
      Sparse.eval value1734 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3028 (1 : Fin 5) = raw2167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3028 raw2167; decide +kernel
    rw [heq]
    exact (canonical2167 hH).trans (sound1734 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3028 (2 : Fin 5)) =
      Sparse.eval value2443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3028 (2 : Fin 5) = raw2260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3028 raw2260; decide +kernel
    rw [heq]
    exact (canonical2260 hH).trans (sound2443 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3028 (3 : Fin 5)) =
      Sparse.eval value1775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3028 (3 : Fin 5) = raw2273 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3028 raw2273; decide +kernel
    rw [heq]
    exact (canonical2273 hH).trans (sound1775 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3028 (4 : Fin 5)) =
      Sparse.eval value1776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3028 (4 : Fin 5) = raw2276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3028 raw2276; decide +kernel
    rw [heq]
    exact (canonical2276 hH).trans (sound1776 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3028 + (injectiveMoment H (mergeFirst pivotMatrix3028 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3028 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3028 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3028 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3028 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3028, value1496, value1734, value1775, value1776, value2443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3029 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3029 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound3029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3029 = Sparse.eval value3029 (momentVector H) := by
  have heq : pivotMatrix3029 = (fun u v => node3029 (pivotPermutation3029 u) v) := by apply Matrix.ext; unfold pivotMatrix3029 node3029 pivotPermutation3029; decide +kernel
  have hmoment : injectiveMoment H node3029 = injectiveMoment H pivotMatrix3029 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3029 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3029 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3029 (0 : Fin 5)) =
      Sparse.eval value1494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3029 (0 : Fin 5) = raw1198 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3029 raw1198; decide +kernel
    rw [heq]
    exact (canonical1198 hH).trans (sound1494 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3029 (1 : Fin 5)) =
      Sparse.eval value1735 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3029 (1 : Fin 5) = raw2170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3029 raw2170; decide +kernel
    rw [heq]
    exact (canonical2170 hH).trans (sound1735 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3029 (2 : Fin 5)) =
      Sparse.eval value2441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3029 (2 : Fin 5) = raw2268 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3029 raw2268; decide +kernel
    rw [heq]
    exact (canonical2268 hH).trans (sound2441 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3029 (3 : Fin 5)) =
      Sparse.eval value1777 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3029 (3 : Fin 5) = raw2279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3029 raw2279; decide +kernel
    rw [heq]
    exact (canonical2279 hH).trans (sound1777 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3029 (4 : Fin 5)) =
      Sparse.eval value1777 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3029 (4 : Fin 5) = raw2281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3029 raw2281; decide +kernel
    rw [heq]
    exact (canonical2281 hH).trans (sound1777 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3029 + (injectiveMoment H (mergeFirst pivotMatrix3029 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3029 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3029 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3029 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3029 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3029, value1494, value1735, value1777, value2441, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3030 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3030 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound3030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3030 = Sparse.eval value3030 (momentVector H) := by
  have heq : pivotMatrix3030 = (fun u v => node3030 (pivotPermutation3030 u) v) := by apply Matrix.ext; unfold pivotMatrix3030 node3030 pivotPermutation3030; decide +kernel
  have hmoment : injectiveMoment H node3030 = injectiveMoment H pivotMatrix3030 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3030 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3030 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3030 (0 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3030 (0 : Fin 5) = raw1213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3030 raw1213; decide +kernel
    rw [heq]
    exact (canonical1213 hH).trans (sound1507 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3030 (1 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3030 (1 : Fin 5) = raw2195 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3030 raw2195; decide +kernel
    rw [heq]
    exact (canonical2195 hH).trans (sound1749 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3030 (2 : Fin 5)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3030 (2 : Fin 5) = raw2309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3030 raw2309; decide +kernel
    rw [heq]
    exact (canonical2309 hH).trans (sound1053 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3030 (3 : Fin 5)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3030 (3 : Fin 5) = raw2328 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3030 raw2328; decide +kernel
    rw [heq]
    exact (canonical2328 hH).trans (sound1053 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3030 (4 : Fin 5)) =
      Sparse.eval value1791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3030 (4 : Fin 5) = raw2330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3030 raw2330; decide +kernel
    rw [heq]
    exact (canonical2330 hH).trans (sound1791 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3030 + (injectiveMoment H (mergeFirst pivotMatrix3030 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3030 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3030 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3030 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3030 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3030, value1053, value1507, value1749, value1791, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3031 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3031 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound3031 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3031 = Sparse.eval value3031 (momentVector H) := by
  have heq : pivotMatrix3031 = (fun u v => node3031 (pivotPermutation3031 u) v) := by apply Matrix.ext; unfold pivotMatrix3031 node3031 pivotPermutation3031; decide +kernel
  have hmoment : injectiveMoment H node3031 = injectiveMoment H pivotMatrix3031 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3031 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3031 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3031 (0 : Fin 5)) =
      Sparse.eval value1506 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3031 (0 : Fin 5) = raw1214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3031 raw1214; decide +kernel
    rw [heq]
    exact (canonical1214 hH).trans (sound1506 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3031 (1 : Fin 5)) =
      Sparse.eval value1750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3031 (1 : Fin 5) = raw2196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3031 raw2196; decide +kernel
    rw [heq]
    exact (canonical2196 hH).trans (sound1750 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3031 (2 : Fin 5)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3031 (2 : Fin 5) = raw2310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3031 raw2310; decide +kernel
    rw [heq]
    exact (canonical2310 hH).trans (sound1260 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3031 (3 : Fin 5)) =
      Sparse.eval value1792 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3031 (3 : Fin 5) = raw2331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3031 raw2331; decide +kernel
    rw [heq]
    exact (canonical2331 hH).trans (sound1792 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3031 (4 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3031 (4 : Fin 5) = raw2335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3031 raw2335; decide +kernel
    rw [heq]
    exact (canonical2335 hH).trans (sound2448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3031 + (injectiveMoment H (mergeFirst pivotMatrix3031 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3031 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3031 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3031 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3031 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3031, value1260, value1506, value1750, value1792, value2448, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3032 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3032 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound3032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3032 = Sparse.eval value3032 (momentVector H) := by
  have heq : pivotMatrix3032 = (fun u v => node3032 (pivotPermutation3032 u) v) := by apply Matrix.ext; unfold pivotMatrix3032 node3032 pivotPermutation3032; decide +kernel
  have hmoment : injectiveMoment H node3032 = injectiveMoment H pivotMatrix3032 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3032 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3032 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3032 (0 : Fin 5)) =
      Sparse.eval value1508 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3032 (0 : Fin 5) = raw1215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3032 raw1215; decide +kernel
    rw [heq]
    exact (canonical1215 hH).trans (sound1508 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3032 (1 : Fin 5)) =
      Sparse.eval value1751 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3032 (1 : Fin 5) = raw2197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3032 raw2197; decide +kernel
    rw [heq]
    exact (canonical2197 hH).trans (sound1751 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3032 (2 : Fin 5)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3032 (2 : Fin 5) = raw2311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3032 raw2311; decide +kernel
    rw [heq]
    exact (canonical2311 hH).trans (sound1047 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3032 (3 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3032 (3 : Fin 5) = raw2332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3032 raw2332; decide +kernel
    rw [heq]
    exact (canonical2332 hH).trans (sound1793 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3032 (4 : Fin 5)) =
      Sparse.eval value2447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3032 (4 : Fin 5) = raw2336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3032 raw2336; decide +kernel
    rw [heq]
    exact (canonical2336 hH).trans (sound2447 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3032 + (injectiveMoment H (mergeFirst pivotMatrix3032 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3032 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3032 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3032 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3032 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3032, value1047, value1508, value1751, value1793, value2447, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3033 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3033 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3033 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3033 = Sparse.eval value3033 (momentVector H) := by
  have heq : pivotMatrix3033 = (fun u v => node3033 (pivotPermutation3033 u) v) := by apply Matrix.ext; unfold pivotMatrix3033 node3033 pivotPermutation3033; decide +kernel
  have hmoment : injectiveMoment H node3033 = injectiveMoment H pivotMatrix3033 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3033 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3033 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3033 (0 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3033 (0 : Fin 5) = raw1217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3033 raw1217; decide +kernel
    rw [heq]
    exact (canonical1217 hH).trans (sound1507 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3033 (1 : Fin 5)) =
      Sparse.eval value1752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3033 (1 : Fin 5) = raw2199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3033 raw2199; decide +kernel
    rw [heq]
    exact (canonical2199 hH).trans (sound1752 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3033 (2 : Fin 5)) =
      Sparse.eval value2450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3033 (2 : Fin 5) = raw2319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3033 raw2319; decide +kernel
    rw [heq]
    exact (canonical2319 hH).trans (sound2450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3033 (3 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3033 (3 : Fin 5) = raw2343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3033 raw2343; decide +kernel
    rw [heq]
    exact (canonical2343 hH).trans (sound1800 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3033 (4 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3033 (4 : Fin 5) = raw2345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3033 raw2345; decide +kernel
    rw [heq]
    exact (canonical2345 hH).trans (sound1800 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3033 + (injectiveMoment H (mergeFirst pivotMatrix3033 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3033 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3033 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3033 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3033 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3033, value1507, value1752, value1800, value2450, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3034 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3034 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound3034 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3034 = Sparse.eval value3034 (momentVector H) := by
  have heq : pivotMatrix3034 = (fun u v => node3034 (pivotPermutation3034 u) v) := by apply Matrix.ext; unfold pivotMatrix3034 node3034 pivotPermutation3034; decide +kernel
  have hmoment : injectiveMoment H node3034 = injectiveMoment H pivotMatrix3034 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3034 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3034 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3034 (0 : Fin 5)) =
      Sparse.eval value1503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3034 (0 : Fin 5) = raw1221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3034 raw1221; decide +kernel
    rw [heq]
    exact (canonical1221 hH).trans (sound1503 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3034 (1 : Fin 5)) =
      Sparse.eval value1749 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3034 (1 : Fin 5) = raw2202 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3034 raw2202; decide +kernel
    rw [heq]
    exact (canonical2202 hH).trans (sound1749 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3034 (2 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3034 (2 : Fin 5) = raw2335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3034 raw2335; decide +kernel
    rw [heq]
    exact (canonical2335 hH).trans (sound2448 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3034 (3 : Fin 5)) =
      Sparse.eval value1803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3034 (3 : Fin 5) = raw2351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3034 raw2351; decide +kernel
    rw [heq]
    exact (canonical2351 hH).trans (sound1803 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3034 (4 : Fin 5)) =
      Sparse.eval value1803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3034 (4 : Fin 5) = raw2353 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3034 raw2353; decide +kernel
    rw [heq]
    exact (canonical2353 hH).trans (sound1803 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3034 + (injectiveMoment H (mergeFirst pivotMatrix3034 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3034 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3034 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3034 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3034 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3034, value1503, value1749, value1803, value2448, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3035 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3035 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound3035 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3035 = Sparse.eval value3035 (momentVector H) := by
  have heq : pivotMatrix3035 = (fun u v => node3035 (pivotPermutation3035 u) v) := by apply Matrix.ext; unfold pivotMatrix3035 node3035 pivotPermutation3035; decide +kernel
  have hmoment : injectiveMoment H node3035 = injectiveMoment H pivotMatrix3035 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3035 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3035 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3035 (0 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3035 (0 : Fin 5) = raw1243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3035 raw1243; decide +kernel
    rw [heq]
    exact (canonical1243 hH).trans (sound1513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3035 (1 : Fin 5)) =
      Sparse.eval value2443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3035 (1 : Fin 5) = raw2260 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3035 raw2260; decide +kernel
    rw [heq]
    exact (canonical2260 hH).trans (sound2443 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3035 (2 : Fin 5)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3035 (2 : Fin 5) = raw2409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3035 raw2409; decide +kernel
    rw [heq]
    exact (canonical2409 hH).trans (sound1110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3035 (3 : Fin 5)) =
      Sparse.eval value1824 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3035 (3 : Fin 5) = raw2420 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3035 raw2420; decide +kernel
    rw [heq]
    exact (canonical2420 hH).trans (sound1824 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3035 (4 : Fin 5)) =
      Sparse.eval value1825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3035 (4 : Fin 5) = raw2423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3035 raw2423; decide +kernel
    rw [heq]
    exact (canonical2423 hH).trans (sound1825 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3035 + (injectiveMoment H (mergeFirst pivotMatrix3035 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3035 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3035 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3035 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3035 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3035, value1110, value1513, value1824, value1825, value2443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3036 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3036 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound3036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3036 = Sparse.eval value3036 (momentVector H) := by
  have heq : pivotMatrix3036 = (fun u v => node3036 (pivotPermutation3036 u) v) := by apply Matrix.ext; unfold pivotMatrix3036 node3036 pivotPermutation3036; decide +kernel
  have hmoment : injectiveMoment H node3036 = injectiveMoment H pivotMatrix3036 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3036 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3036 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3036 (0 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3036 (0 : Fin 5) = raw1246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3036 raw1246; decide +kernel
    rw [heq]
    exact (canonical1246 hH).trans (sound1513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3036 (1 : Fin 5)) =
      Sparse.eval value2442 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3036 (1 : Fin 5) = raw2265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3036 raw2265; decide +kernel
    rw [heq]
    exact (canonical2265 hH).trans (sound2442 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3036 (2 : Fin 5)) =
      Sparse.eval value2449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3036 (2 : Fin 5) = raw2412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3036 raw2412; decide +kernel
    rw [heq]
    exact (canonical2412 hH).trans (sound2449 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3036 (3 : Fin 5)) =
      Sparse.eval value1826 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3036 (3 : Fin 5) = raw2425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3036 raw2425; decide +kernel
    rw [heq]
    exact (canonical2425 hH).trans (sound1826 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3036 (4 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3036 (4 : Fin 5) = raw2427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3036 raw2427; decide +kernel
    rw [heq]
    exact (canonical2427 hH).trans (sound1786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3036 + (injectiveMoment H (mergeFirst pivotMatrix3036 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3036 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3036 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3036 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3036 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3036, value1513, value1786, value1826, value2442, value2449, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3037 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3037 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound3037 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3037 = Sparse.eval value3037 (momentVector H) := by
  have heq : pivotMatrix3037 = (fun u v => node3037 (pivotPermutation3037 u) v) := by apply Matrix.ext; unfold pivotMatrix3037 node3037 pivotPermutation3037; decide +kernel
  have hmoment : injectiveMoment H node3037 = injectiveMoment H pivotMatrix3037 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3037 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3037 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3037 (0 : Fin 5)) =
      Sparse.eval value1512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3037 (0 : Fin 5) = raw1258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3037 raw1258; decide +kernel
    rw [heq]
    exact (canonical1258 hH).trans (sound1512 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3037 (1 : Fin 5)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3037 (1 : Fin 5) = raw2300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3037 raw2300; decide +kernel
    rw [heq]
    exact (canonical2300 hH).trans (sound1040 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3037 (2 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3037 (2 : Fin 5) = raw2440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3037 raw2440; decide +kernel
    rw [heq]
    exact (canonical2440 hH).trans (sound2448 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3037 (3 : Fin 5)) =
      Sparse.eval value1830 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3037 (3 : Fin 5) = raw2452 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3037 raw2452; decide +kernel
    rw [heq]
    exact (canonical2452 hH).trans (sound1830 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3037 (4 : Fin 5)) =
      Sparse.eval value1830 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3037 (4 : Fin 5) = raw2454 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3037 raw2454; decide +kernel
    rw [heq]
    exact (canonical2454 hH).trans (sound1830 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3037 + (injectiveMoment H (mergeFirst pivotMatrix3037 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3037 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3037 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3037 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3037 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3037, value1040, value1512, value1830, value2448, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3038 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3038 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem sound3038 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3038 = Sparse.eval value3038 (momentVector H) := by
  have heq : pivotMatrix3038 = (fun u v => node3038 (pivotPermutation3038 u) v) := by apply Matrix.ext; unfold pivotMatrix3038 node3038 pivotPermutation3038; decide +kernel
  have hmoment : injectiveMoment H node3038 = injectiveMoment H pivotMatrix3038 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3038 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3038 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3038 (0 : Fin 5)) =
      Sparse.eval value1517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3038 (0 : Fin 5) = raw1286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3038 raw1286; decide +kernel
    rw [heq]
    exact (canonical1286 hH).trans (sound1517 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3038 (1 : Fin 5)) =
      Sparse.eval value2762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3038 (1 : Fin 5) = raw2180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3038 raw2180; decide +kernel
    rw [heq]
    exact (canonical2180 hH).trans (sound2762 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3038 (2 : Fin 5)) =
      Sparse.eval value2762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3038 (2 : Fin 5) = raw2235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3038 raw2235; decide +kernel
    rw [heq]
    exact (canonical2235 hH).trans (sound2762 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3038 (3 : Fin 5)) =
      Sparse.eval value2435 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3038 (3 : Fin 5) = raw2237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3038 raw2237; decide +kernel
    rw [heq]
    exact (canonical2237 hH).trans (sound2435 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3038 (4 : Fin 5)) =
      Sparse.eval value1756 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3038 (4 : Fin 5) = raw2238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3038 raw2238; decide +kernel
    rw [heq]
    exact (canonical2238 hH).trans (sound1756 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3038 + (injectiveMoment H (mergeFirst pivotMatrix3038 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3038 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3038 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3038 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3038 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3038, value1517, value1756, value2435, value2762, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3039 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3039 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound3039 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3039 = Sparse.eval value3039 (momentVector H) := by
  have heq : pivotMatrix3039 = (fun u v => node3039 (pivotPermutation3039 u) v) := by apply Matrix.ext; unfold pivotMatrix3039 node3039 pivotPermutation3039; decide +kernel
  have hmoment : injectiveMoment H node3039 = injectiveMoment H pivotMatrix3039 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3039 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3039 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3039 (0 : Fin 5)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3039 (0 : Fin 5) = raw1289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3039 raw1289; decide +kernel
    rw [heq]
    exact (canonical1289 hH).trans (sound1521 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3039 (1 : Fin 5)) =
      Sparse.eval value2830 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3039 (1 : Fin 5) = raw2183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3039 raw2183; decide +kernel
    rw [heq]
    exact (canonical2183 hH).trans (sound2830 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3039 (2 : Fin 5)) =
      Sparse.eval value2439 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3039 (2 : Fin 5) = raw2244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3039 raw2244; decide +kernel
    rw [heq]
    exact (canonical2244 hH).trans (sound2439 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3039 (3 : Fin 5)) =
      Sparse.eval value2439 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3039 (3 : Fin 5) = raw2255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3039 raw2255; decide +kernel
    rw [heq]
    exact (canonical2255 hH).trans (sound2439 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3039 (4 : Fin 5)) =
      Sparse.eval value2778 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3039 (4 : Fin 5) = raw2256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3039 raw2256; decide +kernel
    rw [heq]
    exact (canonical2256 hH).trans (sound2778 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3039 + (injectiveMoment H (mergeFirst pivotMatrix3039 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3039 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3039 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3039 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3039 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3039, value1521, value2439, value2778, value2830, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3040 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3040 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3040 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3040 = Sparse.eval value3040 (momentVector H) := by
  have heq : pivotMatrix3040 = (fun u v => node3040 (pivotPermutation3040 u) v) := by apply Matrix.ext; unfold pivotMatrix3040 node3040 pivotPermutation3040; decide +kernel
  have hmoment : injectiveMoment H node3040 = injectiveMoment H pivotMatrix3040 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3040 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3040 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3040 (0 : Fin 5)) =
      Sparse.eval value1521 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3040 (0 : Fin 5) = raw1291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3040 raw1291; decide +kernel
    rw [heq]
    exact (canonical1291 hH).trans (sound1521 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3040 (1 : Fin 5)) =
      Sparse.eval value2831 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3040 (1 : Fin 5) = raw2184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3040 raw2184; decide +kernel
    rw [heq]
    exact (canonical2184 hH).trans (sound2831 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3040 (2 : Fin 5)) =
      Sparse.eval value2781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3040 (2 : Fin 5) = raw2261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3040 raw2261; decide +kernel
    rw [heq]
    exact (canonical2261 hH).trans (sound2781 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3040 (3 : Fin 5)) =
      Sparse.eval value1774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3040 (3 : Fin 5) = raw2270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3040 raw2270; decide +kernel
    rw [heq]
    exact (canonical2270 hH).trans (sound1774 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3040 (4 : Fin 5)) =
      Sparse.eval value1774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3040 (4 : Fin 5) = raw2271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3040 raw2271; decide +kernel
    rw [heq]
    exact (canonical2271 hH).trans (sound1774 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3040 + (injectiveMoment H (mergeFirst pivotMatrix3040 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3040 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3040 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3040 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3040 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3040, value1521, value1774, value2781, value2831, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3041 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3041 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound3041 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3041 = Sparse.eval value3041 (momentVector H) := by
  have heq : pivotMatrix3041 = (fun u v => node3041 (pivotPermutation3041 u) v) := by apply Matrix.ext; unfold pivotMatrix3041 node3041 pivotPermutation3041; decide +kernel
  have hmoment : injectiveMoment H node3041 = injectiveMoment H pivotMatrix3041 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3041 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3041 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3041 (0 : Fin 5)) =
      Sparse.eval value1518 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3041 (0 : Fin 5) = raw1293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3041 raw1293; decide +kernel
    rw [heq]
    exact (canonical1293 hH).trans (sound1518 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3041 (1 : Fin 5)) =
      Sparse.eval value2814 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3041 (1 : Fin 5) = raw2186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3041 raw2186; decide +kernel
    rw [heq]
    exact (canonical2186 hH).trans (sound2814 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3041 (2 : Fin 5)) =
      Sparse.eval value2442 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3041 (2 : Fin 5) = raw2265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3041 raw2265; decide +kernel
    rw [heq]
    exact (canonical2265 hH).trans (sound2442 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3041 (3 : Fin 5)) =
      Sparse.eval value2769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3041 (3 : Fin 5) = raw2274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3041 raw2274; decide +kernel
    rw [heq]
    exact (canonical2274 hH).trans (sound2769 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3041 (4 : Fin 5)) =
      Sparse.eval value1776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3041 (4 : Fin 5) = raw2276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3041 raw2276; decide +kernel
    rw [heq]
    exact (canonical2276 hH).trans (sound1776 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3041 + (injectiveMoment H (mergeFirst pivotMatrix3041 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3041 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3041 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3041 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3041 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3041, value1518, value1776, value2442, value2769, value2814, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3042 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3042 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3042 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3042 = Sparse.eval value3042 (momentVector H) := by
  have heq : pivotMatrix3042 = (fun u v => node3042 (pivotPermutation3042 u) v) := by apply Matrix.ext; unfold pivotMatrix3042 node3042 pivotPermutation3042; decide +kernel
  have hmoment : injectiveMoment H node3042 = injectiveMoment H pivotMatrix3042 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3042 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3042 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3042 (0 : Fin 5)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3042 (0 : Fin 5) = raw1303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3042 raw1303; decide +kernel
    rw [heq]
    exact (canonical1303 hH).trans (sound1523 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3042 (1 : Fin 5)) =
      Sparse.eval value2781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3042 (1 : Fin 5) = raw2261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3042 raw2261; decide +kernel
    rw [heq]
    exact (canonical2261 hH).trans (sound2781 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3042 (2 : Fin 5)) =
      Sparse.eval value2450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3042 (2 : Fin 5) = raw2390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3042 raw2390; decide +kernel
    rw [heq]
    exact (canonical2390 hH).trans (sound2450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3042 (3 : Fin 5)) =
      Sparse.eval value1819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3042 (3 : Fin 5) = raw2395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3042 raw2395; decide +kernel
    rw [heq]
    exact (canonical2395 hH).trans (sound1819 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3042 (4 : Fin 5)) =
      Sparse.eval value1819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3042 (4 : Fin 5) = raw2396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3042 raw2396; decide +kernel
    rw [heq]
    exact (canonical2396 hH).trans (sound1819 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3042 + (injectiveMoment H (mergeFirst pivotMatrix3042 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3042 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3042 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3042 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3042 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3042, value1523, value1819, value2450, value2781, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3043 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3043 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound3043 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3043 = Sparse.eval value3043 (momentVector H) := by
  have heq : pivotMatrix3043 = (fun u v => node3043 (pivotPermutation3043 u) v) := by apply Matrix.ext; unfold pivotMatrix3043 node3043 pivotPermutation3043; decide +kernel
  have hmoment : injectiveMoment H node3043 = injectiveMoment H pivotMatrix3043 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3043 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3043 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3043 (0 : Fin 5)) =
      Sparse.eval value1524 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3043 (0 : Fin 5) = raw1308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3043 raw1308; decide +kernel
    rw [heq]
    exact (canonical1308 hH).trans (sound1524 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3043 (1 : Fin 5)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3043 (1 : Fin 5) = raw2292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3043 raw2292; decide +kernel
    rw [heq]
    exact (canonical2292 hH).trans (sound1039 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3043 (2 : Fin 5)) =
      Sparse.eval value1039 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3043 (2 : Fin 5) = raw2410 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3043 raw2410; decide +kernel
    rw [heq]
    exact (canonical2410 hH).trans (sound1039 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3043 (3 : Fin 5)) =
      Sparse.eval value1823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3043 (3 : Fin 5) = raw2417 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3043 raw2417; decide +kernel
    rw [heq]
    exact (canonical2417 hH).trans (sound1823 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3043 (4 : Fin 5)) =
      Sparse.eval value1823 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3043 (4 : Fin 5) = raw2418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3043 raw2418; decide +kernel
    rw [heq]
    exact (canonical2418 hH).trans (sound1823 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3043 + (injectiveMoment H (mergeFirst pivotMatrix3043 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3043 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3043 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3043 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3043 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3043, value1039, value1524, value1823, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3044 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3044 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound3044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3044 = Sparse.eval value3044 (momentVector H) := by
  have heq : pivotMatrix3044 = (fun u v => node3044 (pivotPermutation3044 u) v) := by apply Matrix.ext; unfold pivotMatrix3044 node3044 pivotPermutation3044; decide +kernel
  have hmoment : injectiveMoment H node3044 = injectiveMoment H pivotMatrix3044 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3044 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3044 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3044 (0 : Fin 5)) =
      Sparse.eval value1525 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3044 (0 : Fin 5) = raw1310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3044 raw1310; decide +kernel
    rw [heq]
    exact (canonical1310 hH).trans (sound1525 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3044 (1 : Fin 5)) =
      Sparse.eval value1044 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3044 (1 : Fin 5) = raw2297 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3044 raw2297; decide +kernel
    rw [heq]
    exact (canonical2297 hH).trans (sound1044 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3044 (2 : Fin 5)) =
      Sparse.eval value2449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3044 (2 : Fin 5) = raw2412 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3044 raw2412; decide +kernel
    rw [heq]
    exact (canonical2412 hH).trans (sound2449 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3044 (3 : Fin 5)) =
      Sparse.eval value2449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3044 (3 : Fin 5) = raw2421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3044 raw2421; decide +kernel
    rw [heq]
    exact (canonical2421 hH).trans (sound2449 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3044 (4 : Fin 5)) =
      Sparse.eval value1825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3044 (4 : Fin 5) = raw2423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3044 raw2423; decide +kernel
    rw [heq]
    exact (canonical2423 hH).trans (sound1825 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3044 + (injectiveMoment H (mergeFirst pivotMatrix3044 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3044 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3044 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3044 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3044 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3044, value1044, value1525, value1825, value2449, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3045 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3045 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem sound3045 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3045 = Sparse.eval value3045 (momentVector H) := by
  have heq : pivotMatrix3045 = (fun u v => node3045 (pivotPermutation3045 u) v) := by apply Matrix.ext; unfold pivotMatrix3045 node3045 pivotPermutation3045; decide +kernel
  have hmoment : injectiveMoment H node3045 = injectiveMoment H pivotMatrix3045 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3045 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3045 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3045 (0 : Fin 5)) =
      Sparse.eval value1523 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3045 (0 : Fin 5) = raw1318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3045 raw1318; decide +kernel
    rw [heq]
    exact (canonical1318 hH).trans (sound1523 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3045 (1 : Fin 5)) =
      Sparse.eval value2447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3045 (1 : Fin 5) = raw2334 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3045 raw2334; decide +kernel
    rw [heq]
    exact (canonical2334 hH).trans (sound2447 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3045 (2 : Fin 5)) =
      Sparse.eval value2447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3045 (2 : Fin 5) = raw2439 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3045 raw2439; decide +kernel
    rw [heq]
    exact (canonical2439 hH).trans (sound2447 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3045 (3 : Fin 5)) =
      Sparse.eval value2647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3045 (3 : Fin 5) = raw2446 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3045 raw2446; decide +kernel
    rw [heq]
    exact (canonical2446 hH).trans (sound2647 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3045 (4 : Fin 5)) =
      Sparse.eval value1829 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3045 (4 : Fin 5) = raw2449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3045 raw2449; decide +kernel
    rw [heq]
    exact (canonical2449 hH).trans (sound1829 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3045 + (injectiveMoment H (mergeFirst pivotMatrix3045 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3045 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3045 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3045 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3045 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3045, value1523, value1829, value2447, value2647, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3046 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3046 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound3046 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3046 = Sparse.eval value3046 (momentVector H) := by
  have heq : pivotMatrix3046 = (fun u v => node3046 (pivotPermutation3046 u) v) := by apply Matrix.ext; unfold pivotMatrix3046 node3046 pivotPermutation3046; decide +kernel
  have hmoment : injectiveMoment H node3046 = injectiveMoment H pivotMatrix3046 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3046 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3046 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3046 (0 : Fin 5)) =
      Sparse.eval value1524 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3046 (0 : Fin 5) = raw1319 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3046 raw1319; decide +kernel
    rw [heq]
    exact (canonical1319 hH).trans (sound1524 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3046 (1 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3046 (1 : Fin 5) = raw2335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3046 raw2335; decide +kernel
    rw [heq]
    exact (canonical2335 hH).trans (sound2448 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3046 (2 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3046 (2 : Fin 5) = raw2440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3046 raw2440; decide +kernel
    rw [heq]
    exact (canonical2440 hH).trans (sound2448 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3046 (3 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3046 (3 : Fin 5) = raw2447 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3046 raw2447; decide +kernel
    rw [heq]
    exact (canonical2447 hH).trans (sound2448 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3046 (4 : Fin 5)) =
      Sparse.eval value2448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3046 (4 : Fin 5) = raw2450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3046 raw2450; decide +kernel
    rw [heq]
    exact (canonical2450 hH).trans (sound2448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3046 + (injectiveMoment H (mergeFirst pivotMatrix3046 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3046 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3046 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3046 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3046 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3046, value1524, value2448, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3047 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3047 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound3047 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3047 = Sparse.eval value3047 (momentVector H) := by
  have heq : pivotMatrix3047 = (fun u v => node3047 (pivotPermutation3047 u) v) := by apply Matrix.ext; unfold pivotMatrix3047 node3047 pivotPermutation3047; decide +kernel
  have hmoment : injectiveMoment H node3047 = injectiveMoment H pivotMatrix3047 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3047 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3047 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3047 (0 : Fin 5)) =
      Sparse.eval value1813 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3047 (0 : Fin 5) = raw2551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3047 raw2551; decide +kernel
    rw [heq]
    exact (canonical2551 hH).trans (sound1813 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3047 (1 : Fin 5)) =
      Sparse.eval value1768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3047 (1 : Fin 5) = raw2252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3047 raw2252; decide +kernel
    rw [heq]
    exact (canonical2252 hH).trans (sound1768 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3047 (2 : Fin 5)) =
      Sparse.eval value1758 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3047 (2 : Fin 5) = raw2213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3047 raw2213; decide +kernel
    rw [heq]
    exact (canonical2213 hH).trans (sound1758 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3047 (3 : Fin 5)) =
      Sparse.eval value1755 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3047 (3 : Fin 5) = raw2209 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3047 raw2209; decide +kernel
    rw [heq]
    exact (canonical2209 hH).trans (sound1755 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3047 (4 : Fin 5)) =
      Sparse.eval value1754 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3047 (4 : Fin 5) = raw2208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3047 raw2208; decide +kernel
    rw [heq]
    exact (canonical2208 hH).trans (sound1754 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3047 + (injectiveMoment H (mergeFirst pivotMatrix3047 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3047 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3047 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3047 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3047 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3047, value1754, value1755, value1758, value1768, value1813, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3048 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3048 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem sound3048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3048 = Sparse.eval value3048 (momentVector H) := by
  have heq : pivotMatrix3048 = (fun u v => node3048 (pivotPermutation3048 u) v) := by apply Matrix.ext; unfold pivotMatrix3048 node3048 pivotPermutation3048; decide +kernel
  have hmoment : injectiveMoment H node3048 = injectiveMoment H pivotMatrix3048 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3048 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3048 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3048 (0 : Fin 5)) =
      Sparse.eval value1843 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3048 (0 : Fin 5) = raw2552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3048 raw2552; decide +kernel
    rw [heq]
    exact (canonical2552 hH).trans (sound1843 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3048 (1 : Fin 5)) =
      Sparse.eval value2778 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3048 (1 : Fin 5) = raw2256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3048 raw2256; decide +kernel
    rw [heq]
    exact (canonical2256 hH).trans (sound2778 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3048 (2 : Fin 5)) =
      Sparse.eval value1757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3048 (2 : Fin 5) = raw2217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3048 raw2217; decide +kernel
    rw [heq]
    exact (canonical2217 hH).trans (sound1757 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3048 (3 : Fin 5)) =
      Sparse.eval value1757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3048 (3 : Fin 5) = raw2212 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3048 raw2212; decide +kernel
    rw [heq]
    exact (canonical2212 hH).trans (sound1757 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3048 (4 : Fin 5)) =
      Sparse.eval value1756 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3048 (4 : Fin 5) = raw2211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3048 raw2211; decide +kernel
    rw [heq]
    exact (canonical2211 hH).trans (sound1756 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3048 + (injectiveMoment H (mergeFirst pivotMatrix3048 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3048 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3048 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3048 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3048 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3048, value1756, value1757, value1843, value2778, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3049 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3049 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound3049 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3049 = Sparse.eval value3049 (momentVector H) := by
  have heq : pivotMatrix3049 = (fun u v => node3049 (pivotPermutation3049 u) v) := by apply Matrix.ext; unfold pivotMatrix3049 node3049 pivotPermutation3049; decide +kernel
  have hmoment : injectiveMoment H node3049 = injectiveMoment H pivotMatrix3049 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3049 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3049 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3049 (0 : Fin 5)) =
      Sparse.eval value1845 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3049 (0 : Fin 5) = raw2557 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3049 raw2557; decide +kernel
    rw [heq]
    exact (canonical2557 hH).trans (sound1845 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3049 (1 : Fin 5)) =
      Sparse.eval value2769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3049 (1 : Fin 5) = raw2274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3049 raw2274; decide +kernel
    rw [heq]
    exact (canonical2274 hH).trans (sound2769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3049 (2 : Fin 5)) =
      Sparse.eval value1670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3049 (2 : Fin 5) = raw2222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3049 raw2222; decide +kernel
    rw [heq]
    exact (canonical2222 hH).trans (sound1670 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3049 (3 : Fin 5)) =
      Sparse.eval value1761 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3049 (3 : Fin 5) = raw2220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3049 raw2220; decide +kernel
    rw [heq]
    exact (canonical2220 hH).trans (sound1761 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3049 (4 : Fin 5)) =
      Sparse.eval value1760 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3049 (4 : Fin 5) = raw2219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3049 raw2219; decide +kernel
    rw [heq]
    exact (canonical2219 hH).trans (sound1760 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3049 + (injectiveMoment H (mergeFirst pivotMatrix3049 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3049 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3049 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3049 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3049 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3049, value1670, value1760, value1761, value1845, value2769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3050 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3050 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3050 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3050 = Sparse.eval value3050 (momentVector H) := by
  have heq : pivotMatrix3050 = (fun u v => node3050 (pivotPermutation3050 u) v) := by apply Matrix.ext; unfold pivotMatrix3050 node3050 pivotPermutation3050; decide +kernel
  have hmoment : injectiveMoment H node3050 = injectiveMoment H pivotMatrix3050 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3050 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3050 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3050 (0 : Fin 5)) =
      Sparse.eval value1814 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3050 (0 : Fin 5) = raw2559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3050 raw2559; decide +kernel
    rw [heq]
    exact (canonical2559 hH).trans (sound1814 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3050 (1 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3050 (1 : Fin 5) = raw2278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3050 raw2278; decide +kernel
    rw [heq]
    exact (canonical2278 hH).trans (sound1718 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3050 (2 : Fin 5)) =
      Sparse.eval value1763 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3050 (2 : Fin 5) = raw2225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3050 raw2225; decide +kernel
    rw [heq]
    exact (canonical2225 hH).trans (sound1763 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3050 (3 : Fin 5)) =
      Sparse.eval value1762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3050 (3 : Fin 5) = raw2223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3050 raw2223; decide +kernel
    rw [heq]
    exact (canonical2223 hH).trans (sound1762 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3050 (4 : Fin 5)) =
      Sparse.eval value1670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3050 (4 : Fin 5) = raw2222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3050 raw2222; decide +kernel
    rw [heq]
    exact (canonical2222 hH).trans (sound1670 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3050 + (injectiveMoment H (mergeFirst pivotMatrix3050 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3050 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3050 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3050 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3050 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3050, value1670, value1718, value1762, value1763, value1814, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3051 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3051 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound3051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3051 = Sparse.eval value3051 (momentVector H) := by
  have heq : pivotMatrix3051 = (fun u v => node3051 (pivotPermutation3051 u) v) := by apply Matrix.ext; unfold pivotMatrix3051 node3051 pivotPermutation3051; decide +kernel
  have hmoment : injectiveMoment H node3051 = injectiveMoment H pivotMatrix3051 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3051 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3051 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3051 (0 : Fin 5)) =
      Sparse.eval value2761 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3051 (0 : Fin 5) = raw3732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3051 raw3732; decide +kernel
    rw [heq]
    exact (canonical3732 hH).trans (sound2761 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3051 (1 : Fin 5)) =
      Sparse.eval value1819 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3051 (1 : Fin 5) = raw2395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3051 raw2395; decide +kernel
    rw [heq]
    exact (canonical2395 hH).trans (sound1819 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3051 (2 : Fin 5)) =
      Sparse.eval value1761 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3051 (2 : Fin 5) = raw2220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3051 raw2220; decide +kernel
    rw [heq]
    exact (canonical2220 hH).trans (sound1761 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3051 (3 : Fin 5)) =
      Sparse.eval value2432 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3051 (3 : Fin 5) = raw2215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3051 raw2215; decide +kernel
    rw [heq]
    exact (canonical2215 hH).trans (sound2432 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3051 (4 : Fin 5)) =
      Sparse.eval value1759 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3051 (4 : Fin 5) = raw2214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3051 raw2214; decide +kernel
    rw [heq]
    exact (canonical2214 hH).trans (sound1759 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3051 + (injectiveMoment H (mergeFirst pivotMatrix3051 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3051 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3051 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3051 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3051 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3051, value1759, value1761, value1819, value2432, value2761, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3052 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3052 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem sound3052 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3052 = Sparse.eval value3052 (momentVector H) := by
  have heq : pivotMatrix3052 = (fun u v => node3052 (pivotPermutation3052 u) v) := by apply Matrix.ext; unfold pivotMatrix3052 node3052 pivotPermutation3052; decide +kernel
  have hmoment : injectiveMoment H node3052 = injectiveMoment H pivotMatrix3052 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3052 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3052 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3052 (0 : Fin 5)) =
      Sparse.eval value1563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3052 (0 : Fin 5) = raw1841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3052 raw1841; decide +kernel
    rw [heq]
    exact (canonical1841 hH).trans (sound1563 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3052 (1 : Fin 5)) =
      Sparse.eval value1754 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3052 (1 : Fin 5) = raw2208 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3052 raw2208; decide +kernel
    rw [heq]
    exact (canonical2208 hH).trans (sound1754 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3052 (2 : Fin 5)) =
      Sparse.eval value1764 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3052 (2 : Fin 5) = raw2246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3052 raw2246; decide +kernel
    rw [heq]
    exact (canonical2246 hH).trans (sound1764 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3052 (3 : Fin 5)) =
      Sparse.eval value1767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3052 (3 : Fin 5) = raw2251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3052 raw2251; decide +kernel
    rw [heq]
    exact (canonical2251 hH).trans (sound1767 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3052 (4 : Fin 5)) =
      Sparse.eval value1768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3052 (4 : Fin 5) = raw2252 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3052 raw2252; decide +kernel
    rw [heq]
    exact (canonical2252 hH).trans (sound1768 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3052 + (injectiveMoment H (mergeFirst pivotMatrix3052 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3052 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3052 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3052 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3052 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3052, value1563, value1754, value1764, value1767, value1768, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3053 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3053 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound3053 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3053 = Sparse.eval value3053 (momentVector H) := by
  have heq : pivotMatrix3053 = (fun u v => node3053 (pivotPermutation3053 u) v) := by apply Matrix.ext; unfold pivotMatrix3053 node3053 pivotPermutation3053; decide +kernel
  have hmoment : injectiveMoment H node3053 = injectiveMoment H pivotMatrix3053 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3053 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3053 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3053 (0 : Fin 5)) =
      Sparse.eval value2626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3053 (0 : Fin 5) = raw1851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3053 raw1851; decide +kernel
    rw [heq]
    exact (canonical1851 hH).trans (sound2626 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3053 (1 : Fin 5)) =
      Sparse.eval value1761 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3053 (1 : Fin 5) = raw2220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3053 raw2220; decide +kernel
    rw [heq]
    exact (canonical2220 hH).trans (sound1761 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3053 (2 : Fin 5)) =
      Sparse.eval value1774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3053 (2 : Fin 5) = raw2270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3053 raw2270; decide +kernel
    rw [heq]
    exact (canonical2270 hH).trans (sound1774 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3053 (3 : Fin 5)) =
      Sparse.eval value2769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3053 (3 : Fin 5) = raw2274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3053 raw2274; decide +kernel
    rw [heq]
    exact (canonical2274 hH).trans (sound2769 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3053 (4 : Fin 5)) =
      Sparse.eval value1776 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3053 (4 : Fin 5) = raw2275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3053 raw2275; decide +kernel
    rw [heq]
    exact (canonical2275 hH).trans (sound1776 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3053 + (injectiveMoment H (mergeFirst pivotMatrix3053 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3053 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3053 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3053 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3053 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3053, value1761, value1774, value1776, value2626, value2769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3054 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3054 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3054 = Sparse.eval value3054 (momentVector H) := by
  have heq : pivotMatrix3054 = (fun u v => node3054 (pivotPermutation3054 u) v) := by apply Matrix.ext; unfold pivotMatrix3054 node3054 pivotPermutation3054; decide +kernel
  have hmoment : injectiveMoment H node3054 = injectiveMoment H pivotMatrix3054 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3054 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3054 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3054 (0 : Fin 5)) =
      Sparse.eval value1486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3054 (0 : Fin 5) = raw1857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3054 raw1857; decide +kernel
    rw [heq]
    exact (canonical1857 hH).trans (sound1486 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3054 (1 : Fin 5)) =
      Sparse.eval value1763 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3054 (1 : Fin 5) = raw2225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3054 raw2225; decide +kernel
    rw [heq]
    exact (canonical2225 hH).trans (sound1763 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3054 (2 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3054 (2 : Fin 5) = raw2278 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3054 raw2278; decide +kernel
    rw [heq]
    exact (canonical2278 hH).trans (sound1718 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3054 (3 : Fin 5)) =
      Sparse.eval value1777 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3054 (3 : Fin 5) = raw2279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3054 raw2279; decide +kernel
    rw [heq]
    exact (canonical2279 hH).trans (sound1777 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3054 (4 : Fin 5)) =
      Sparse.eval value1778 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3054 (4 : Fin 5) = raw2280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3054 raw2280; decide +kernel
    rw [heq]
    exact (canonical2280 hH).trans (sound1778 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3054 + (injectiveMoment H (mergeFirst pivotMatrix3054 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3054 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3054 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3054 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3054 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3054, value1486, value1718, value1763, value1777, value1778, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3055 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3055 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound3055 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3055 = Sparse.eval value3055 (momentVector H) := by
  have heq : pivotMatrix3055 = (fun u v => node3055 (pivotPermutation3055 u) v) := by apply Matrix.ext; unfold pivotMatrix3055 node3055 pivotPermutation3055; decide +kernel
  have hmoment : injectiveMoment H node3055 = injectiveMoment H pivotMatrix3055 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3055 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3055 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3055 (0 : Fin 5)) =
      Sparse.eval value1678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3055 (0 : Fin 5) = raw1891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3055 raw1891; decide +kernel
    rw [heq]
    exact (canonical1891 hH).trans (sound1678 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3055 (1 : Fin 5)) =
      Sparse.eval value1249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3055 (1 : Fin 5) = raw2286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3055 raw2286; decide +kernel
    rw [heq]
    exact (canonical2286 hH).trans (sound1249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3055 (2 : Fin 5)) =
      Sparse.eval value1779 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3055 (2 : Fin 5) = raw2313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3055 raw2313; decide +kernel
    rw [heq]
    exact (canonical2313 hH).trans (sound1779 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3055 (3 : Fin 5)) =
      Sparse.eval value1783 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3055 (3 : Fin 5) = raw2317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3055 raw2317; decide +kernel
    rw [heq]
    exact (canonical2317 hH).trans (sound1783 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3055 (4 : Fin 5)) =
      Sparse.eval value1784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3055 (4 : Fin 5) = raw2318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3055 raw2318; decide +kernel
    rw [heq]
    exact (canonical2318 hH).trans (sound1784 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3055 + (injectiveMoment H (mergeFirst pivotMatrix3055 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3055 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3055 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3055 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3055 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3055, value1249, value1678, value1779, value1783, value1784, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3056 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3056 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem sound3056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3056 = Sparse.eval value3056 (momentVector H) := by
  have heq : pivotMatrix3056 = (fun u v => node3056 (pivotPermutation3056 u) v) := by apply Matrix.ext; unfold pivotMatrix3056 node3056 pivotPermutation3056; decide +kernel
  have hmoment : injectiveMoment H node3056 = injectiveMoment H pivotMatrix3056 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3056 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3056 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3056 (0 : Fin 5)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3056 (0 : Fin 5) = raw1895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3056 raw1895; decide +kernel
    rw [heq]
    exact (canonical1895 hH).trans (sound1680 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3056 (1 : Fin 5)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3056 (1 : Fin 5) = raw2287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3056 raw2287; decide +kernel
    rw [heq]
    exact (canonical2287 hH).trans (sound1107 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3056 (2 : Fin 5)) =
      Sparse.eval value1780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3056 (2 : Fin 5) = raw2314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3056 raw2314; decide +kernel
    rw [heq]
    exact (canonical2314 hH).trans (sound1780 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3056 (3 : Fin 5)) =
      Sparse.eval value1780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3056 (3 : Fin 5) = raw2320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3056 raw2320; decide +kernel
    rw [heq]
    exact (canonical2320 hH).trans (sound1780 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3056 (4 : Fin 5)) =
      Sparse.eval value1785 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3056 (4 : Fin 5) = raw2321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3056 raw2321; decide +kernel
    rw [heq]
    exact (canonical2321 hH).trans (sound1785 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3056 + (injectiveMoment H (mergeFirst pivotMatrix3056 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3056 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3056 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3056 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3056 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3056, value1107, value1680, value1780, value1785, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3057 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3057 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem sound3057 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3057 = Sparse.eval value3057 (momentVector H) := by
  have heq : pivotMatrix3057 = (fun u v => node3057 (pivotPermutation3057 u) v) := by apply Matrix.ext; unfold pivotMatrix3057 node3057 pivotPermutation3057; decide +kernel
  have hmoment : injectiveMoment H node3057 = injectiveMoment H pivotMatrix3057 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3057 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3057 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3057 (0 : Fin 5)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3057 (0 : Fin 5) = raw1896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3057 raw1896; decide +kernel
    rw [heq]
    exact (canonical1896 hH).trans (sound2742 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3057 (1 : Fin 5)) =
      Sparse.eval value1110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3057 (1 : Fin 5) = raw2288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3057 raw2288; decide +kernel
    rw [heq]
    exact (canonical2288 hH).trans (sound1110 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3057 (2 : Fin 5)) =
      Sparse.eval value1781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3057 (2 : Fin 5) = raw2315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3057 raw2315; decide +kernel
    rw [heq]
    exact (canonical2315 hH).trans (sound1781 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3057 (3 : Fin 5)) =
      Sparse.eval value1785 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3057 (3 : Fin 5) = raw2321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3057 raw2321; decide +kernel
    rw [heq]
    exact (canonical2321 hH).trans (sound1785 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3057 (4 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3057 (4 : Fin 5) = raw2322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3057 raw2322; decide +kernel
    rw [heq]
    exact (canonical2322 hH).trans (sound1786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3057 + (injectiveMoment H (mergeFirst pivotMatrix3057 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3057 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3057 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3057 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3057 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3057, value1110, value1781, value1785, value1786, value2742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3058 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3058 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem sound3058 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3058 = Sparse.eval value3058 (momentVector H) := by
  have heq : pivotMatrix3058 = (fun u v => node3058 (pivotPermutation3058 u) v) := by apply Matrix.ext; unfold pivotMatrix3058 node3058 pivotPermutation3058; decide +kernel
  have hmoment : injectiveMoment H node3058 = injectiveMoment H pivotMatrix3058 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3058 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3058 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3058 (0 : Fin 5)) =
      Sparse.eval value1681 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3058 (0 : Fin 5) = raw1897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3058 raw1897; decide +kernel
    rw [heq]
    exact (canonical1897 hH).trans (sound1681 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3058 (1 : Fin 5)) =
      Sparse.eval value1112 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3058 (1 : Fin 5) = raw2289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3058 raw2289; decide +kernel
    rw [heq]
    exact (canonical2289 hH).trans (sound1112 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3058 (2 : Fin 5)) =
      Sparse.eval value1782 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3058 (2 : Fin 5) = raw2316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3058 raw2316; decide +kernel
    rw [heq]
    exact (canonical2316 hH).trans (sound1782 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3058 (3 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3058 (3 : Fin 5) = raw2322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3058 raw2322; decide +kernel
    rw [heq]
    exact (canonical2322 hH).trans (sound1786 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3058 (4 : Fin 5)) =
      Sparse.eval value1787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3058 (4 : Fin 5) = raw2323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3058 raw2323; decide +kernel
    rw [heq]
    exact (canonical2323 hH).trans (sound1787 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3058 + (injectiveMoment H (mergeFirst pivotMatrix3058 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3058 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3058 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3058 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3058 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3058, value1112, value1681, value1782, value1786, value1787, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3059 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3059 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound3059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3059 = Sparse.eval value3059 (momentVector H) := by
  have heq : pivotMatrix3059 = (fun u v => node3059 (pivotPermutation3059 u) v) := by apply Matrix.ext; unfold pivotMatrix3059 node3059 pivotPermutation3059; decide +kernel
  have hmoment : injectiveMoment H node3059 = injectiveMoment H pivotMatrix3059 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3059 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3059 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3059 (0 : Fin 5)) =
      Sparse.eval value1682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3059 (0 : Fin 5) = raw1898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3059 raw1898; decide +kernel
    rw [heq]
    exact (canonical1898 hH).trans (sound1682 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3059 (1 : Fin 5)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3059 (1 : Fin 5) = raw2290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3059 raw2290; decide +kernel
    rw [heq]
    exact (canonical2290 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3059 (2 : Fin 5)) =
      Sparse.eval value1783 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3059 (2 : Fin 5) = raw2317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3059 raw2317; decide +kernel
    rw [heq]
    exact (canonical2317 hH).trans (sound1783 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3059 (3 : Fin 5)) =
      Sparse.eval value1788 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3059 (3 : Fin 5) = raw2324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3059 raw2324; decide +kernel
    rw [heq]
    exact (canonical2324 hH).trans (sound1788 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3059 (4 : Fin 5)) =
      Sparse.eval value1789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3059 (4 : Fin 5) = raw2325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3059 raw2325; decide +kernel
    rw [heq]
    exact (canonical2325 hH).trans (sound1789 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3059 + (injectiveMoment H (mergeFirst pivotMatrix3059 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3059 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3059 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3059 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3059 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3059, value1123, value1682, value1783, value1788, value1789, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3060 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3060 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound3060 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3060 = Sparse.eval value3060 (momentVector H) := by
  have heq : pivotMatrix3060 = (fun u v => node3060 (pivotPermutation3060 u) v) := by apply Matrix.ext; unfold pivotMatrix3060 node3060 pivotPermutation3060; decide +kernel
  have hmoment : injectiveMoment H node3060 = injectiveMoment H pivotMatrix3060 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3060 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3060 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3060 (0 : Fin 5)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3060 (0 : Fin 5) = raw1899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3060 raw1899; decide +kernel
    rw [heq]
    exact (canonical1899 hH).trans (sound2748 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3060 (1 : Fin 5)) =
      Sparse.eval value1265 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3060 (1 : Fin 5) = raw2291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3060 raw2291; decide +kernel
    rw [heq]
    exact (canonical2291 hH).trans (sound1265 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3060 (2 : Fin 5)) =
      Sparse.eval value1784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3060 (2 : Fin 5) = raw2318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3060 raw2318; decide +kernel
    rw [heq]
    exact (canonical2318 hH).trans (sound1784 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3060 (3 : Fin 5)) =
      Sparse.eval value1789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3060 (3 : Fin 5) = raw2325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3060 raw2325; decide +kernel
    rw [heq]
    exact (canonical2325 hH).trans (sound1789 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3060 (4 : Fin 5)) =
      Sparse.eval value1790 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3060 (4 : Fin 5) = raw2326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3060 raw2326; decide +kernel
    rw [heq]
    exact (canonical2326 hH).trans (sound1790 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3060 + (injectiveMoment H (mergeFirst pivotMatrix3060 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3060 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3060 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3060 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3060 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3060, value1265, value1784, value1789, value1790, value2748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3061 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3061 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem sound3061 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3061 = Sparse.eval value3061 (momentVector H) := by
  have heq : pivotMatrix3061 = (fun u v => node3061 (pivotPermutation3061 u) v) := by apply Matrix.ext; unfold pivotMatrix3061 node3061 pivotPermutation3061; decide +kernel
  have hmoment : injectiveMoment H node3061 = injectiveMoment H pivotMatrix3061 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3061 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3061 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3061 (0 : Fin 5)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3061 (0 : Fin 5) = raw1905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3061 raw1905; decide +kernel
    rw [heq]
    exact (canonical1905 hH).trans (sound2676 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3061 (1 : Fin 5)) =
      Sparse.eval value1040 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3061 (1 : Fin 5) = raw2294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3061 raw2294; decide +kernel
    rw [heq]
    exact (canonical2294 hH).trans (sound1040 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3061 (2 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3061 (2 : Fin 5) = raw2322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3061 raw2322; decide +kernel
    rw [heq]
    exact (canonical2322 hH).trans (sound1786 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3061 (3 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3061 (3 : Fin 5) = raw2329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3061 raw2329; decide +kernel
    rw [heq]
    exact (canonical2329 hH).trans (sound1786 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3061 (4 : Fin 5)) =
      Sparse.eval value1791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3061 (4 : Fin 5) = raw2330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3061 raw2330; decide +kernel
    rw [heq]
    exact (canonical2330 hH).trans (sound1791 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3061 + (injectiveMoment H (mergeFirst pivotMatrix3061 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3061 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3061 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3061 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3061 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3061, value1040, value1786, value1791, value2676, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3062 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3062 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound3062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3062 = Sparse.eval value3062 (momentVector H) := by
  have heq : pivotMatrix3062 = (fun u v => node3062 (pivotPermutation3062 u) v) := by apply Matrix.ext; unfold pivotMatrix3062 node3062 pivotPermutation3062; decide +kernel
  have hmoment : injectiveMoment H node3062 = injectiveMoment H pivotMatrix3062 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3062 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3062 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3062 (0 : Fin 5)) =
      Sparse.eval value2767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3062 (0 : Fin 5) = raw1908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3062 raw1908; decide +kernel
    rw [heq]
    exact (canonical1908 hH).trans (sound2767 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3062 (1 : Fin 5)) =
      Sparse.eval value1260 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3062 (1 : Fin 5) = raw2295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3062 raw2295; decide +kernel
    rw [heq]
    exact (canonical2295 hH).trans (sound1260 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3062 (2 : Fin 5)) =
      Sparse.eval value1790 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3062 (2 : Fin 5) = raw2326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3062 raw2326; decide +kernel
    rw [heq]
    exact (canonical2326 hH).trans (sound1790 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3062 (3 : Fin 5)) =
      Sparse.eval value1792 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3062 (3 : Fin 5) = raw2331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3062 raw2331; decide +kernel
    rw [heq]
    exact (canonical2331 hH).trans (sound1792 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3062 (4 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3062 (4 : Fin 5) = raw2332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3062 raw2332; decide +kernel
    rw [heq]
    exact (canonical2332 hH).trans (sound1793 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3062 + (injectiveMoment H (mergeFirst pivotMatrix3062 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3062 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3062 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3062 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3062 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3062, value1260, value1790, value1792, value1793, value2767, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3063 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3063 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound3063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3063 = Sparse.eval value3063 (momentVector H) := by
  have heq : pivotMatrix3063 = (fun u v => node3063 (pivotPermutation3063 u) v) := by apply Matrix.ext; unfold pivotMatrix3063 node3063 pivotPermutation3063; decide +kernel
  have hmoment : injectiveMoment H node3063 = injectiveMoment H pivotMatrix3063 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3063 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3063 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3063 (0 : Fin 5)) =
      Sparse.eval value1685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3063 (0 : Fin 5) = raw1909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3063 raw1909; decide +kernel
    rw [heq]
    exact (canonical1909 hH).trans (sound1685 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3063 (1 : Fin 5)) =
      Sparse.eval value1078 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3063 (1 : Fin 5) = raw2296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3063 raw2296; decide +kernel
    rw [heq]
    exact (canonical2296 hH).trans (sound1078 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3063 (2 : Fin 5)) =
      Sparse.eval value1847 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3063 (2 : Fin 5) = raw2327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3063 raw2327; decide +kernel
    rw [heq]
    exact (canonical2327 hH).trans (sound1847 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3063 (3 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3063 (3 : Fin 5) = raw2332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3063 raw2332; decide +kernel
    rw [heq]
    exact (canonical2332 hH).trans (sound1793 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3063 (4 : Fin 5)) =
      Sparse.eval value1794 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3063 (4 : Fin 5) = raw2333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3063 raw2333; decide +kernel
    rw [heq]
    exact (canonical2333 hH).trans (sound1794 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3063 + (injectiveMoment H (mergeFirst pivotMatrix3063 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3063 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3063 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3063 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3063 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3063, value1078, value1685, value1793, value1794, value1847, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3064 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3064 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound3064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3064 = Sparse.eval value3064 (momentVector H) := by
  have heq : pivotMatrix3064 = (fun u v => node3064 (pivotPermutation3064 u) v) := by apply Matrix.ext; unfold pivotMatrix3064 node3064 pivotPermutation3064; decide +kernel
  have hmoment : injectiveMoment H node3064 = injectiveMoment H pivotMatrix3064 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3064 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3064 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3064 (0 : Fin 5)) =
      Sparse.eval value1686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3064 (0 : Fin 5) = raw1914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3064 raw1914; decide +kernel
    rw [heq]
    exact (canonical1914 hH).trans (sound1686 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3064 (1 : Fin 5)) =
      Sparse.eval value1058 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3064 (1 : Fin 5) = raw2299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3064 raw2299; decide +kernel
    rw [heq]
    exact (canonical2299 hH).trans (sound1058 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3064 (2 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3064 (2 : Fin 5) = raw2332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3064 raw2332; decide +kernel
    rw [heq]
    exact (canonical2332 hH).trans (sound1793 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3064 (3 : Fin 5)) =
      Sparse.eval value1795 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3064 (3 : Fin 5) = raw2338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3064 raw2338; decide +kernel
    rw [heq]
    exact (canonical2338 hH).trans (sound1795 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3064 (4 : Fin 5)) =
      Sparse.eval value1796 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3064 (4 : Fin 5) = raw2339 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3064 raw2339; decide +kernel
    rw [heq]
    exact (canonical2339 hH).trans (sound1796 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3064 + (injectiveMoment H (mergeFirst pivotMatrix3064 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3064 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3064 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3064 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3064 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3064, value1058, value1686, value1793, value1795, value1796, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3065 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3065 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound3065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3065 = Sparse.eval value3065 (momentVector H) := by
  have heq : pivotMatrix3065 = (fun u v => node3065 (pivotPermutation3065 u) v) := by apply Matrix.ext; unfold pivotMatrix3065 node3065 pivotPermutation3065; decide +kernel
  have hmoment : injectiveMoment H node3065 = injectiveMoment H pivotMatrix3065 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3065 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3065 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3065 (0 : Fin 5)) =
      Sparse.eval value1687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3065 (0 : Fin 5) = raw1917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3065 raw1917; decide +kernel
    rw [heq]
    exact (canonical1917 hH).trans (sound1687 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3065 (1 : Fin 5)) =
      Sparse.eval value1010 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3065 (1 : Fin 5) = raw2301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3065 raw2301; decide +kernel
    rw [heq]
    exact (canonical2301 hH).trans (sound1010 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3065 (2 : Fin 5)) =
      Sparse.eval value1797 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3065 (2 : Fin 5) = raw2340 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3065 raw2340; decide +kernel
    rw [heq]
    exact (canonical2340 hH).trans (sound1797 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3065 (3 : Fin 5)) =
      Sparse.eval value1799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3065 (3 : Fin 5) = raw2342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3065 raw2342; decide +kernel
    rw [heq]
    exact (canonical2342 hH).trans (sound1799 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3065 (4 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3065 (4 : Fin 5) = raw2343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3065 raw2343; decide +kernel
    rw [heq]
    exact (canonical2343 hH).trans (sound1800 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3065 + (injectiveMoment H (mergeFirst pivotMatrix3065 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3065 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3065 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3065 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3065 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3065, value1010, value1687, value1797, value1799, value1800, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3066 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3066 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound3066 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3066 = Sparse.eval value3066 (momentVector H) := by
  have heq : pivotMatrix3066 = (fun u v => node3066 (pivotPermutation3066 u) v) := by apply Matrix.ext; unfold pivotMatrix3066 node3066 pivotPermutation3066; decide +kernel
  have hmoment : injectiveMoment H node3066 = injectiveMoment H pivotMatrix3066 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3066 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3066 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3066 (0 : Fin 5)) =
      Sparse.eval value1688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3066 (0 : Fin 5) = raw1918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3066 raw1918; decide +kernel
    rw [heq]
    exact (canonical1918 hH).trans (sound1688 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3066 (1 : Fin 5)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3066 (1 : Fin 5) = raw2302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3066 raw2302; decide +kernel
    rw [heq]
    exact (canonical2302 hH).trans (sound1005 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3066 (2 : Fin 5)) =
      Sparse.eval value1798 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3066 (2 : Fin 5) = raw2341 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3066 raw2341; decide +kernel
    rw [heq]
    exact (canonical2341 hH).trans (sound1798 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3066 (3 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3066 (3 : Fin 5) = raw2343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3066 raw2343; decide +kernel
    rw [heq]
    exact (canonical2343 hH).trans (sound1800 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3066 (4 : Fin 5)) =
      Sparse.eval value1848 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3066 (4 : Fin 5) = raw2344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3066 raw2344; decide +kernel
    rw [heq]
    exact (canonical2344 hH).trans (sound1848 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3066 + (injectiveMoment H (mergeFirst pivotMatrix3066 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3066 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3066 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3066 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3066 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3066, value1005, value1688, value1798, value1800, value1848, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3067 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3067 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound3067 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3067 = Sparse.eval value3067 (momentVector H) := by
  have heq : pivotMatrix3067 = (fun u v => node3067 (pivotPermutation3067 u) v) := by apply Matrix.ext; unfold pivotMatrix3067 node3067 pivotPermutation3067; decide +kernel
  have hmoment : injectiveMoment H node3067 = injectiveMoment H pivotMatrix3067 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3067 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3067 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3067 (0 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3067 (0 : Fin 5) = raw1921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3067 raw1921; decide +kernel
    rw [heq]
    exact (canonical1921 hH).trans (sound2750 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3067 (1 : Fin 5)) =
      Sparse.eval value1047 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3067 (1 : Fin 5) = raw2303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3067 raw2303; decide +kernel
    rw [heq]
    exact (canonical2303 hH).trans (sound1047 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3067 (2 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3067 (2 : Fin 5) = raw2343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3067 raw2343; decide +kernel
    rw [heq]
    exact (canonical2343 hH).trans (sound1800 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3067 (3 : Fin 5)) =
      Sparse.eval value1801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3067 (3 : Fin 5) = raw2347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3067 raw2347; decide +kernel
    rw [heq]
    exact (canonical2347 hH).trans (sound1801 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3067 (4 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3067 (4 : Fin 5) = raw2348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3067 raw2348; decide +kernel
    rw [heq]
    exact (canonical2348 hH).trans (sound1793 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3067 + (injectiveMoment H (mergeFirst pivotMatrix3067 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3067 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3067 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3067 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3067 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3067, value1047, value1793, value1800, value1801, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3068 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3068 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound3068 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3068 = Sparse.eval value3068 (momentVector H) := by
  have heq : pivotMatrix3068 = (fun u v => node3068 (pivotPermutation3068 u) v) := by apply Matrix.ext; unfold pivotMatrix3068 node3068 pivotPermutation3068; decide +kernel
  have hmoment : injectiveMoment H node3068 = injectiveMoment H pivotMatrix3068 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3068 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3068 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3068 (0 : Fin 5)) =
      Sparse.eval value2619 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3068 (0 : Fin 5) = raw1925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3068 raw1925; decide +kernel
    rw [heq]
    exact (canonical1925 hH).trans (sound2619 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3068 (1 : Fin 5)) =
      Sparse.eval value837 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3068 (1 : Fin 5) = raw2304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3068 raw2304; decide +kernel
    rw [heq]
    exact (canonical2304 hH).trans (sound837 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3068 (2 : Fin 5)) =
      Sparse.eval value1801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3068 (2 : Fin 5) = raw2347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3068 raw2347; decide +kernel
    rw [heq]
    exact (canonical2347 hH).trans (sound1801 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3068 (3 : Fin 5)) =
      Sparse.eval value1802 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3068 (3 : Fin 5) = raw2350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3068 raw2350; decide +kernel
    rw [heq]
    exact (canonical2350 hH).trans (sound1802 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3068 (4 : Fin 5)) =
      Sparse.eval value1803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3068 (4 : Fin 5) = raw2351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3068 raw2351; decide +kernel
    rw [heq]
    exact (canonical2351 hH).trans (sound1803 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3068 + (injectiveMoment H (mergeFirst pivotMatrix3068 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3068 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3068 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3068 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3068 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3068, value1801, value1802, value1803, value2619, value837, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3069 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3069 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3069 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3069 = Sparse.eval value3069 (momentVector H) := by
  have heq : pivotMatrix3069 = (fun u v => node3069 (pivotPermutation3069 u) v) := by apply Matrix.ext; unfold pivotMatrix3069 node3069 pivotPermutation3069; decide +kernel
  have hmoment : injectiveMoment H node3069 = injectiveMoment H pivotMatrix3069 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3069 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3069 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3069 (0 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3069 (0 : Fin 5) = raw1926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3069 raw1926; decide +kernel
    rw [heq]
    exact (canonical1926 hH).trans (sound2740 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3069 (1 : Fin 5)) =
      Sparse.eval value1053 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3069 (1 : Fin 5) = raw2305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3069 raw2305; decide +kernel
    rw [heq]
    exact (canonical2305 hH).trans (sound1053 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3069 (2 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3069 (2 : Fin 5) = raw2348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3069 raw2348; decide +kernel
    rw [heq]
    exact (canonical2348 hH).trans (sound1793 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3069 (3 : Fin 5)) =
      Sparse.eval value1803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3069 (3 : Fin 5) = raw2351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3069 raw2351; decide +kernel
    rw [heq]
    exact (canonical2351 hH).trans (sound1803 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3069 (4 : Fin 5)) =
      Sparse.eval value1804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3069 (4 : Fin 5) = raw2352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3069 raw2352; decide +kernel
    rw [heq]
    exact (canonical2352 hH).trans (sound1804 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3069 + (injectiveMoment H (mergeFirst pivotMatrix3069 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3069 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3069 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3069 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3069 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3069, value1053, value1793, value1803, value1804, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3070 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3070 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound3070 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3070 = Sparse.eval value3070 (momentVector H) := by
  have heq : pivotMatrix3070 = (fun u v => node3070 (pivotPermutation3070 u) v) := by apply Matrix.ext; unfold pivotMatrix3070 node3070 pivotPermutation3070; decide +kernel
  have hmoment : injectiveMoment H node3070 = injectiveMoment H pivotMatrix3070 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3070 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3070 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3070 (0 : Fin 5)) =
      Sparse.eval value1624 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3070 (0 : Fin 5) = raw1930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3070 raw1930; decide +kernel
    rw [heq]
    exact (canonical1930 hH).trans (sound1624 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3070 (1 : Fin 5)) =
      Sparse.eval value1013 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3070 (1 : Fin 5) = raw2306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3070 raw2306; decide +kernel
    rw [heq]
    exact (canonical2306 hH).trans (sound1013 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3070 (2 : Fin 5)) =
      Sparse.eval value1803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3070 (2 : Fin 5) = raw2351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3070 raw2351; decide +kernel
    rw [heq]
    exact (canonical2351 hH).trans (sound1803 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3070 (3 : Fin 5)) =
      Sparse.eval value1805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3070 (3 : Fin 5) = raw2354 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3070 raw2354; decide +kernel
    rw [heq]
    exact (canonical2354 hH).trans (sound1805 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3070 (4 : Fin 5)) =
      Sparse.eval value1806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3070 (4 : Fin 5) = raw2355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3070 raw2355; decide +kernel
    rw [heq]
    exact (canonical2355 hH).trans (sound1806 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3070 + (injectiveMoment H (mergeFirst pivotMatrix3070 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3070 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3070 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3070 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3070 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3070, value1013, value1624, value1803, value1805, value1806, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3071 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3071 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound3071 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3071 = Sparse.eval value3071 (momentVector H) := by
  have heq : pivotMatrix3071 = (fun u v => node3071 (pivotPermutation3071 u) v) := by apply Matrix.ext; unfold pivotMatrix3071 node3071 pivotPermutation3071; decide +kernel
  have hmoment : injectiveMoment H node3071 = injectiveMoment H pivotMatrix3071 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3071 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3071 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3071 (0 : Fin 5)) =
      Sparse.eval value1626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3071 (0 : Fin 5) = raw1931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3071 raw1931; decide +kernel
    rw [heq]
    exact (canonical1931 hH).trans (sound1626 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3071 (1 : Fin 5)) =
      Sparse.eval value1016 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3071 (1 : Fin 5) = raw2307 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3071 raw2307; decide +kernel
    rw [heq]
    exact (canonical2307 hH).trans (sound1016 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3071 (2 : Fin 5)) =
      Sparse.eval value1804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3071 (2 : Fin 5) = raw2352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3071 raw2352; decide +kernel
    rw [heq]
    exact (canonical2352 hH).trans (sound1804 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3071 (3 : Fin 5)) =
      Sparse.eval value1806 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3071 (3 : Fin 5) = raw2355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3071 raw2355; decide +kernel
    rw [heq]
    exact (canonical2355 hH).trans (sound1806 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3071 (4 : Fin 5)) =
      Sparse.eval value1807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3071 (4 : Fin 5) = raw2356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3071 raw2356; decide +kernel
    rw [heq]
    exact (canonical2356 hH).trans (sound1807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3071 + (injectiveMoment H (mergeFirst pivotMatrix3071 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3071 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3071 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3071 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3071 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3071, value1016, value1626, value1804, value1806, value1807, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
