import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values22
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical57
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical107

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2944 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2944 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem sound2944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2944 = Sparse.eval value2944 (momentVector H) := by
  have heq : pivotMatrix2944 = (fun u v => node2944 (pivotPermutation2944 u) v) := by apply Matrix.ext; unfold pivotMatrix2944 node2944 pivotPermutation2944; decide +kernel
  have hmoment : injectiveMoment H node2944 = injectiveMoment H pivotMatrix2944 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2944 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2944 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2944 (0 : Fin 5)) =
      Sparse.eval value1459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2944 (0 : Fin 5) = raw1040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2944 raw1040; decide +kernel
    rw [heq]
    exact (canonical1040 hH).trans (sound1459 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2944 (1 : Fin 5)) =
      Sparse.eval value1631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2944 (1 : Fin 5) = raw1761 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2944 raw1761; decide +kernel
    rw [heq]
    exact (canonical1761 hH).trans (sound1631 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2944 (2 : Fin 5)) =
      Sparse.eval value1631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2944 (2 : Fin 5) = raw1871 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2944 raw1871; decide +kernel
    rw [heq]
    exact (canonical1871 hH).trans (sound1631 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2944 (3 : Fin 5)) =
      Sparse.eval value967 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2944 (3 : Fin 5) = raw1879 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2944 raw1879; decide +kernel
    rw [heq]
    exact (canonical1879 hH).trans (sound967 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2944 (4 : Fin 5)) =
      Sparse.eval value2421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2944 (4 : Fin 5) = raw1881 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2944 raw1881; decide +kernel
    rw [heq]
    exact (canonical1881 hH).trans (sound2421 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2944 + (injectiveMoment H (mergeFirst pivotMatrix2944 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2944 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2944 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2944 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2944 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2944, value1459, value1631, value2421, value967, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2945 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2945 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem sound2945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2945 = Sparse.eval value2945 (momentVector H) := by
  have heq : pivotMatrix2945 = (fun u v => node2945 (pivotPermutation2945 u) v) := by apply Matrix.ext; unfold pivotMatrix2945 node2945 pivotPermutation2945; decide +kernel
  have hmoment : injectiveMoment H node2945 = injectiveMoment H pivotMatrix2945 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2945 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2945 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2945 (0 : Fin 5)) =
      Sparse.eval value1458 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2945 (0 : Fin 5) = raw1044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2945 raw1044; decide +kernel
    rw [heq]
    exact (canonical1044 hH).trans (sound1458 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2945 (1 : Fin 5)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2945 (1 : Fin 5) = raw1762 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2945 raw1762; decide +kernel
    rw [heq]
    exact (canonical1762 hH).trans (sound1634 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2945 (2 : Fin 5)) =
      Sparse.eval value1634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2945 (2 : Fin 5) = raw1872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2945 raw1872; decide +kernel
    rw [heq]
    exact (canonical1872 hH).trans (sound1634 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2945 (3 : Fin 5)) =
      Sparse.eval value1673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2945 (3 : Fin 5) = raw1883 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2945 raw1883; decide +kernel
    rw [heq]
    exact (canonical1883 hH).trans (sound1673 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2945 (4 : Fin 5)) =
      Sparse.eval value2419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2945 (4 : Fin 5) = raw1885 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2945 raw1885; decide +kernel
    rw [heq]
    exact (canonical1885 hH).trans (sound2419 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2945 + (injectiveMoment H (mergeFirst pivotMatrix2945 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2945 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2945 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2945 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2945 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2945, value1458, value1634, value1673, value2419, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2946 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2946 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2946 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2946 = Sparse.eval value2946 (momentVector H) := by
  have heq : pivotMatrix2946 = (fun u v => node2946 (pivotPermutation2946 u) v) := by apply Matrix.ext; unfold pivotMatrix2946 node2946 pivotPermutation2946; decide +kernel
  have hmoment : injectiveMoment H node2946 = injectiveMoment H pivotMatrix2946 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2946 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2946 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2946 (0 : Fin 5)) =
      Sparse.eval value1467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2946 (0 : Fin 5) = raw1075 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2946 raw1075; decide +kernel
    rw [heq]
    exact (canonical1075 hH).trans (sound1467 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2946 (1 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2946 (1 : Fin 5) = raw1766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2946 raw1766; decide +kernel
    rw [heq]
    exact (canonical1766 hH).trans (sound1644 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2946 (2 : Fin 5)) =
      Sparse.eval value2424 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2946 (2 : Fin 5) = raw1915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2946 raw1915; decide +kernel
    rw [heq]
    exact (canonical1915 hH).trans (sound2424 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2946 (3 : Fin 5)) =
      Sparse.eval value1624 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2946 (3 : Fin 5) = raw1930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2946 raw1930; decide +kernel
    rw [heq]
    exact (canonical1930 hH).trans (sound1624 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2946 (4 : Fin 5)) =
      Sparse.eval value1624 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2946 (4 : Fin 5) = raw1932 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2946 raw1932; decide +kernel
    rw [heq]
    exact (canonical1932 hH).trans (sound1624 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2946 + (injectiveMoment H (mergeFirst pivotMatrix2946 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2946 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2946 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2946 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2946 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2946, value1467, value1624, value1644, value2424, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2947 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2947 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound2947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2947 = Sparse.eval value2947 (momentVector H) := by
  have heq : pivotMatrix2947 = (fun u v => node2947 (pivotPermutation2947 u) v) := by apply Matrix.ext; unfold pivotMatrix2947 node2947 pivotPermutation2947; decide +kernel
  have hmoment : injectiveMoment H node2947 = injectiveMoment H pivotMatrix2947 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2947 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2947 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2947 (0 : Fin 5)) =
      Sparse.eval value1475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2947 (0 : Fin 5) = raw1083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2947 raw1083; decide +kernel
    rw [heq]
    exact (canonical1083 hH).trans (sound1475 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2947 (1 : Fin 5)) =
      Sparse.eval value1646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2947 (1 : Fin 5) = raw1772 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2947 raw1772; decide +kernel
    rw [heq]
    exact (canonical1772 hH).trans (sound1646 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2947 (2 : Fin 5)) =
      Sparse.eval value2413 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2947 (2 : Fin 5) = raw1940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2947 raw1940; decide +kernel
    rw [heq]
    exact (canonical1940 hH).trans (sound2413 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2947 (3 : Fin 5)) =
      Sparse.eval value2413 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2947 (3 : Fin 5) = raw1950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2947 raw1950; decide +kernel
    rw [heq]
    exact (canonical1950 hH).trans (sound2413 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2947 (4 : Fin 5)) =
      Sparse.eval value1695 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2947 (4 : Fin 5) = raw1952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2947 raw1952; decide +kernel
    rw [heq]
    exact (canonical1952 hH).trans (sound1695 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2947 + (injectiveMoment H (mergeFirst pivotMatrix2947 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2947 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2947 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2947 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2947 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2947, value1475, value1646, value1695, value2413, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2948 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2948 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound2948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2948 = Sparse.eval value2948 (momentVector H) := by
  have heq : pivotMatrix2948 = (fun u v => node2948 (pivotPermutation2948 u) v) := by apply Matrix.ext; unfold pivotMatrix2948 node2948 pivotPermutation2948; decide +kernel
  have hmoment : injectiveMoment H node2948 = injectiveMoment H pivotMatrix2948 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2948 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2948 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2948 (0 : Fin 5)) =
      Sparse.eval value1476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2948 (0 : Fin 5) = raw1084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2948 raw1084; decide +kernel
    rw [heq]
    exact (canonical1084 hH).trans (sound1476 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2948 (1 : Fin 5)) =
      Sparse.eval value1647 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2948 (1 : Fin 5) = raw1773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2948 raw1773; decide +kernel
    rw [heq]
    exact (canonical1773 hH).trans (sound1647 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2948 (2 : Fin 5)) =
      Sparse.eval value2412 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2948 (2 : Fin 5) = raw1941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2948 raw1941; decide +kernel
    rw [heq]
    exact (canonical1941 hH).trans (sound2412 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2948 (3 : Fin 5)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2948 (3 : Fin 5) = raw1951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2948 raw1951; decide +kernel
    rw [heq]
    exact (canonical1951 hH).trans (sound807 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2948 (4 : Fin 5)) =
      Sparse.eval value1696 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2948 (4 : Fin 5) = raw1953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2948 raw1953; decide +kernel
    rw [heq]
    exact (canonical1953 hH).trans (sound1696 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2948 + (injectiveMoment H (mergeFirst pivotMatrix2948 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2948 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2948 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2948 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2948 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2948, value1476, value1647, value1696, value2412, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2949 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2949 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound2949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2949 = Sparse.eval value2949 (momentVector H) := by
  have heq : pivotMatrix2949 = (fun u v => node2949 (pivotPermutation2949 u) v) := by apply Matrix.ext; unfold pivotMatrix2949 node2949 pivotPermutation2949; decide +kernel
  have hmoment : injectiveMoment H node2949 = injectiveMoment H pivotMatrix2949 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2949 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2949 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2949 (0 : Fin 5)) =
      Sparse.eval value1477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2949 (0 : Fin 5) = raw1085 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2949 raw1085; decide +kernel
    rw [heq]
    exact (canonical1085 hH).trans (sound1477 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2949 (1 : Fin 5)) =
      Sparse.eval value1648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2949 (1 : Fin 5) = raw1774 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2949 raw1774; decide +kernel
    rw [heq]
    exact (canonical1774 hH).trans (sound1648 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2949 (2 : Fin 5)) =
      Sparse.eval value2410 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2949 (2 : Fin 5) = raw1942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2949 raw1942; decide +kernel
    rw [heq]
    exact (canonical1942 hH).trans (sound2410 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2949 (3 : Fin 5)) =
      Sparse.eval value1697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2949 (3 : Fin 5) = raw1954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2949 raw1954; decide +kernel
    rw [heq]
    exact (canonical1954 hH).trans (sound1697 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2949 (4 : Fin 5)) =
      Sparse.eval value2428 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2949 (4 : Fin 5) = raw1956 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2949 raw1956; decide +kernel
    rw [heq]
    exact (canonical1956 hH).trans (sound2428 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2949 + (injectiveMoment H (mergeFirst pivotMatrix2949 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2949 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2949 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2949 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2949 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2949, value1477, value1648, value1697, value2410, value2428, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2950 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2950 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound2950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2950 = Sparse.eval value2950 (momentVector H) := by
  have heq : pivotMatrix2950 = (fun u v => node2950 (pivotPermutation2950 u) v) := by apply Matrix.ext; unfold pivotMatrix2950 node2950 pivotPermutation2950; decide +kernel
  have hmoment : injectiveMoment H node2950 = injectiveMoment H pivotMatrix2950 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2950 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2950 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2950 (0 : Fin 5)) =
      Sparse.eval value1478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2950 (0 : Fin 5) = raw1086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2950 raw1086; decide +kernel
    rw [heq]
    exact (canonical1086 hH).trans (sound1478 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2950 (1 : Fin 5)) =
      Sparse.eval value1649 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2950 (1 : Fin 5) = raw1775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2950 raw1775; decide +kernel
    rw [heq]
    exact (canonical1775 hH).trans (sound1649 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2950 (2 : Fin 5)) =
      Sparse.eval value2411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2950 (2 : Fin 5) = raw1943 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2950 raw1943; decide +kernel
    rw [heq]
    exact (canonical1943 hH).trans (sound2411 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2950 (3 : Fin 5)) =
      Sparse.eval value1698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2950 (3 : Fin 5) = raw1955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2950 raw1955; decide +kernel
    rw [heq]
    exact (canonical1955 hH).trans (sound1698 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2950 (4 : Fin 5)) =
      Sparse.eval value2428 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2950 (4 : Fin 5) = raw1957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2950 raw1957; decide +kernel
    rw [heq]
    exact (canonical1957 hH).trans (sound2428 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2950 + (injectiveMoment H (mergeFirst pivotMatrix2950 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2950 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2950 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2950 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2950 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2950, value1478, value1649, value1698, value2411, value2428, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2951 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2951 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound2951 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2951 = Sparse.eval value2951 (momentVector H) := by
  have heq : pivotMatrix2951 = (fun u v => node2951 (pivotPermutation2951 u) v) := by apply Matrix.ext; unfold pivotMatrix2951 node2951 pivotPermutation2951; decide +kernel
  have hmoment : injectiveMoment H node2951 = injectiveMoment H pivotMatrix2951 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2951 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2951 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2951 (0 : Fin 5)) =
      Sparse.eval value1478 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2951 (0 : Fin 5) = raw1090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2951 raw1090; decide +kernel
    rw [heq]
    exact (canonical1090 hH).trans (sound1478 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2951 (1 : Fin 5)) =
      Sparse.eval value1652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2951 (1 : Fin 5) = raw1780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2951 raw1780; decide +kernel
    rw [heq]
    exact (canonical1780 hH).trans (sound1652 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2951 (2 : Fin 5)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2951 (2 : Fin 5) = raw1944 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2951 raw1944; decide +kernel
    rw [heq]
    exact (canonical1944 hH).trans (sound805 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2951 (3 : Fin 5)) =
      Sparse.eval value1700 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2951 (3 : Fin 5) = raw1960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2951 raw1960; decide +kernel
    rw [heq]
    exact (canonical1960 hH).trans (sound1700 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2951 (4 : Fin 5)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2951 (4 : Fin 5) = raw1963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2951 raw1963; decide +kernel
    rw [heq]
    exact (canonical1963 hH).trans (sound2427 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2951 + (injectiveMoment H (mergeFirst pivotMatrix2951 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2951 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2951 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2951 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2951 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2951, value1478, value1652, value1700, value2427, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2952 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2952 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2952 = Sparse.eval value2952 (momentVector H) := by
  have heq : pivotMatrix2952 = (fun u v => node2952 (pivotPermutation2952 u) v) := by apply Matrix.ext; unfold pivotMatrix2952 node2952 pivotPermutation2952; decide +kernel
  have hmoment : injectiveMoment H node2952 = injectiveMoment H pivotMatrix2952 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2952 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2952 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2952 (0 : Fin 5)) =
      Sparse.eval value1475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2952 (0 : Fin 5) = raw1097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2952 raw1097; decide +kernel
    rw [heq]
    exact (canonical1097 hH).trans (sound1475 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2952 (1 : Fin 5)) =
      Sparse.eval value1657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2952 (1 : Fin 5) = raw1790 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2952 raw1790; decide +kernel
    rw [heq]
    exact (canonical1790 hH).trans (sound1657 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2952 (2 : Fin 5)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2952 (2 : Fin 5) = raw1963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2952 raw1963; decide +kernel
    rw [heq]
    exact (canonical1963 hH).trans (sound2427 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2952 (3 : Fin 5)) =
      Sparse.eval value1705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2952 (3 : Fin 5) = raw1971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2952 raw1971; decide +kernel
    rw [heq]
    exact (canonical1971 hH).trans (sound1705 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2952 (4 : Fin 5)) =
      Sparse.eval value1705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2952 (4 : Fin 5) = raw1973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2952 raw1973; decide +kernel
    rw [heq]
    exact (canonical1973 hH).trans (sound1705 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2952 + (injectiveMoment H (mergeFirst pivotMatrix2952 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2952 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2952 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2952 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2952 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2952, value1475, value1657, value1705, value2427, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2953 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2953 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem sound2953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2953 = Sparse.eval value2953 (momentVector H) := by
  have heq : pivotMatrix2953 = (fun u v => node2953 (pivotPermutation2953 u) v) := by apply Matrix.ext; unfold pivotMatrix2953 node2953 pivotPermutation2953; decide +kernel
  have hmoment : injectiveMoment H node2953 = injectiveMoment H pivotMatrix2953 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2953 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2953 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2953 (0 : Fin 5)) =
      Sparse.eval value1483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2953 (0 : Fin 5) = raw1115 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2953 raw1115; decide +kernel
    rw [heq]
    exact (canonical1115 hH).trans (sound1483 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2953 (1 : Fin 5)) =
      Sparse.eval value2417 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2953 (1 : Fin 5) = raw1842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2953 raw1842; decide +kernel
    rw [heq]
    exact (canonical1842 hH).trans (sound2417 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2953 (2 : Fin 5)) =
      Sparse.eval value2417 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2953 (2 : Fin 5) = raw2007 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2953 raw2007; decide +kernel
    rw [heq]
    exact (canonical2007 hH).trans (sound2417 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2953 (3 : Fin 5)) =
      Sparse.eval value1714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2953 (3 : Fin 5) = raw2016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2953 raw2016; decide +kernel
    rw [heq]
    exact (canonical2016 hH).trans (sound1714 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2953 (4 : Fin 5)) =
      Sparse.eval value1717 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2953 (4 : Fin 5) = raw2021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2953 raw2021; decide +kernel
    rw [heq]
    exact (canonical2021 hH).trans (sound1717 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2953 + (injectiveMoment H (mergeFirst pivotMatrix2953 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2953 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2953 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2953 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2953 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2953, value1483, value1714, value1717, value2417, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2954 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2954 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem sound2954 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2954 = Sparse.eval value2954 (momentVector H) := by
  have heq : pivotMatrix2954 = (fun u v => node2954 (pivotPermutation2954 u) v) := by apply Matrix.ext; unfold pivotMatrix2954 node2954 pivotPermutation2954; decide +kernel
  have hmoment : injectiveMoment H node2954 = injectiveMoment H pivotMatrix2954 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2954 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2954 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2954 (0 : Fin 5)) =
      Sparse.eval value1486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2954 (0 : Fin 5) = raw1119 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2954 raw1119; decide +kernel
    rw [heq]
    exact (canonical1119 hH).trans (sound1486 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2954 (1 : Fin 5)) =
      Sparse.eval value2416 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2954 (1 : Fin 5) = raw1844 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2954 raw1844; decide +kernel
    rw [heq]
    exact (canonical1844 hH).trans (sound2416 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2954 (2 : Fin 5)) =
      Sparse.eval value1063 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2954 (2 : Fin 5) = raw2008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2954 raw2008; decide +kernel
    rw [heq]
    exact (canonical2008 hH).trans (sound1063 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2954 (3 : Fin 5)) =
      Sparse.eval value1671 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2954 (3 : Fin 5) = raw2024 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2954 raw2024; decide +kernel
    rw [heq]
    exact (canonical2024 hH).trans (sound1671 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2954 (4 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2954 (4 : Fin 5) = raw2028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2954 raw2028; decide +kernel
    rw [heq]
    exact (canonical2028 hH).trans (sound1718 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2954 + (injectiveMoment H (mergeFirst pivotMatrix2954 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2954 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2954 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2954 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2954 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2954, value1063, value1486, value1671, value1718, value2416, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2955 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2955 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2955 = Sparse.eval value2955 (momentVector H) := by
  have heq : pivotMatrix2955 = (fun u v => node2955 (pivotPermutation2955 u) v) := by apply Matrix.ext; unfold pivotMatrix2955 node2955 pivotPermutation2955; decide +kernel
  have hmoment : injectiveMoment H node2955 = injectiveMoment H pivotMatrix2955 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2955 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2955 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2955 (0 : Fin 5)) =
      Sparse.eval value1486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2955 (0 : Fin 5) = raw1125 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2955 raw1125; decide +kernel
    rw [heq]
    exact (canonical1125 hH).trans (sound1486 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2955 (1 : Fin 5)) =
      Sparse.eval value2415 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2955 (1 : Fin 5) = raw1847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2955 raw1847; decide +kernel
    rw [heq]
    exact (canonical1847 hH).trans (sound2415 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2955 (2 : Fin 5)) =
      Sparse.eval value2428 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2955 (2 : Fin 5) = raw2011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2955 raw2011; decide +kernel
    rw [heq]
    exact (canonical2011 hH).trans (sound2428 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2955 (3 : Fin 5)) =
      Sparse.eval value1669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2955 (3 : Fin 5) = raw2034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2955 raw2034; decide +kernel
    rw [heq]
    exact (canonical2034 hH).trans (sound1669 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2955 (4 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2955 (4 : Fin 5) = raw2037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2955 raw2037; decide +kernel
    rw [heq]
    exact (canonical2037 hH).trans (sound1720 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2955 + (injectiveMoment H (mergeFirst pivotMatrix2955 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2955 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2955 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2955 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2955 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2955, value1486, value1669, value1720, value2415, value2428, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2956 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2956 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2956 = Sparse.eval value2956 (momentVector H) := by
  have heq : pivotMatrix2956 = (fun u v => node2956 (pivotPermutation2956 u) v) := by apply Matrix.ext; unfold pivotMatrix2956 node2956 pivotPermutation2956; decide +kernel
  have hmoment : injectiveMoment H node2956 = injectiveMoment H pivotMatrix2956 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2956 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2956 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2956 (0 : Fin 5)) =
      Sparse.eval value1483 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2956 (0 : Fin 5) = raw1127 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2956 raw1127; decide +kernel
    rw [heq]
    exact (canonical1127 hH).trans (sound1483 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2956 (1 : Fin 5)) =
      Sparse.eval value2414 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2956 (1 : Fin 5) = raw1850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2956 raw1850; decide +kernel
    rw [heq]
    exact (canonical1850 hH).trans (sound2414 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2956 (2 : Fin 5)) =
      Sparse.eval value2430 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2956 (2 : Fin 5) = raw2013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2956 raw2013; decide +kernel
    rw [heq]
    exact (canonical2013 hH).trans (sound2430 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2956 (3 : Fin 5)) =
      Sparse.eval value1722 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2956 (3 : Fin 5) = raw2039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2956 raw2039; decide +kernel
    rw [heq]
    exact (canonical2039 hH).trans (sound1722 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2956 (4 : Fin 5)) =
      Sparse.eval value1722 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2956 (4 : Fin 5) = raw2041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2956 raw2041; decide +kernel
    rw [heq]
    exact (canonical2041 hH).trans (sound1722 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2956 + (injectiveMoment H (mergeFirst pivotMatrix2956 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2956 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2956 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2956 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2956 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2956, value1483, value1722, value2414, value2430, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2957 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2957 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2957 = Sparse.eval value2957 (momentVector H) := by
  have heq : pivotMatrix2957 = (fun u v => node2957 (pivotPermutation2957 u) v) := by apply Matrix.ext; unfold pivotMatrix2957 node2957 pivotPermutation2957; decide +kernel
  have hmoment : injectiveMoment H node2957 = injectiveMoment H pivotMatrix2957 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2957 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2957 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2957 (0 : Fin 5)) =
      Sparse.eval value1484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2957 (0 : Fin 5) = raw1140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2957 raw1140; decide +kernel
    rw [heq]
    exact (canonical1140 hH).trans (sound1484 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2957 (1 : Fin 5)) =
      Sparse.eval value1041 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2957 (1 : Fin 5) = raw1867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2957 raw1867; decide +kernel
    rw [heq]
    exact (canonical1867 hH).trans (sound1041 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2957 (2 : Fin 5)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2957 (2 : Fin 5) = raw2052 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2957 raw2052; decide +kernel
    rw [heq]
    exact (canonical2052 hH).trans (sound2427 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2957 (3 : Fin 5)) =
      Sparse.eval value1625 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2957 (3 : Fin 5) = raw2064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2957 raw2064; decide +kernel
    rw [heq]
    exact (canonical2064 hH).trans (sound1625 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2957 (4 : Fin 5)) =
      Sparse.eval value1625 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2957 (4 : Fin 5) = raw2066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2957 raw2066; decide +kernel
    rw [heq]
    exact (canonical2066 hH).trans (sound1625 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2957 + (injectiveMoment H (mergeFirst pivotMatrix2957 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2957 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2957 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2957 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2957 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2957, value1041, value1484, value1625, value2427, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2958 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2958 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

theorem sound2958 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2958 = Sparse.eval value2958 (momentVector H) := by
  have heq : pivotMatrix2958 = (fun u v => node2958 (pivotPermutation2958 u) v) := by apply Matrix.ext; unfold pivotMatrix2958 node2958 pivotPermutation2958; decide +kernel
  have hmoment : injectiveMoment H node2958 = injectiveMoment H pivotMatrix2958 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2958 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2958 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2958 (0 : Fin 5)) =
      Sparse.eval value1491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2958 (0 : Fin 5) = raw1177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2958 raw1177; decide +kernel
    rw [heq]
    exact (canonical1177 hH).trans (sound1491 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2958 (1 : Fin 5)) =
      Sparse.eval value2406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2958 (1 : Fin 5) = raw1752 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2958 raw1752; decide +kernel
    rw [heq]
    exact (canonical1752 hH).trans (sound2406 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2958 (2 : Fin 5)) =
      Sparse.eval value2406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2958 (2 : Fin 5) = raw1821 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2958 raw1821; decide +kernel
    rw [heq]
    exact (canonical1821 hH).trans (sound2406 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2958 (3 : Fin 5)) =
      Sparse.eval value2405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2958 (3 : Fin 5) = raw1824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2958 raw1824; decide +kernel
    rw [heq]
    exact (canonical1824 hH).trans (sound2405 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2958 (4 : Fin 5)) =
      Sparse.eval value1664 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2958 (4 : Fin 5) = raw1825 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2958 raw1825; decide +kernel
    rw [heq]
    exact (canonical1825 hH).trans (sound1664 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2958 + (injectiveMoment H (mergeFirst pivotMatrix2958 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2958 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2958 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2958 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2958 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2958, value1491, value1664, value2405, value2406, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2959 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2959 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem sound2959 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2959 = Sparse.eval value2959 (momentVector H) := by
  have heq : pivotMatrix2959 = (fun u v => node2959 (pivotPermutation2959 u) v) := by apply Matrix.ext; unfold pivotMatrix2959 node2959 pivotPermutation2959; decide +kernel
  have hmoment : injectiveMoment H node2959 = injectiveMoment H pivotMatrix2959 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2959 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2959 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2959 (0 : Fin 5)) =
      Sparse.eval value1492 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2959 (0 : Fin 5) = raw1179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2959 raw1179; decide +kernel
    rw [heq]
    exact (canonical1179 hH).trans (sound1492 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2959 (1 : Fin 5)) =
      Sparse.eval value2737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2959 (1 : Fin 5) = raw1753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2959 raw1753; decide +kernel
    rw [heq]
    exact (canonical1753 hH).trans (sound2737 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2959 (2 : Fin 5)) =
      Sparse.eval value1629 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2959 (2 : Fin 5) = raw1823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2959 raw1823; decide +kernel
    rw [heq]
    exact (canonical1823 hH).trans (sound1629 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2959 (3 : Fin 5)) =
      Sparse.eval value1197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2959 (3 : Fin 5) = raw1829 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2959 raw1829; decide +kernel
    rw [heq]
    exact (canonical1829 hH).trans (sound1197 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2959 (4 : Fin 5)) =
      Sparse.eval value2409 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2959 (4 : Fin 5) = raw1831 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2959 raw1831; decide +kernel
    rw [heq]
    exact (canonical1831 hH).trans (sound2409 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2959 + (injectiveMoment H (mergeFirst pivotMatrix2959 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2959 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2959 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2959 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2959 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2959, value1197, value1492, value1629, value2409, value2737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2960 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2960 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem sound2960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2960 = Sparse.eval value2960 (momentVector H) := by
  have heq : pivotMatrix2960 = (fun u v => node2960 (pivotPermutation2960 u) v) := by apply Matrix.ext; unfold pivotMatrix2960 node2960 pivotPermutation2960; decide +kernel
  have hmoment : injectiveMoment H node2960 = injectiveMoment H pivotMatrix2960 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2960 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2960 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2960 (0 : Fin 5)) =
      Sparse.eval value1494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2960 (0 : Fin 5) = raw1181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2960 raw1181; decide +kernel
    rw [heq]
    exact (canonical1181 hH).trans (sound1494 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2960 (1 : Fin 5)) =
      Sparse.eval value1467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2960 (1 : Fin 5) = raw1754 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2960 raw1754; decide +kernel
    rw [heq]
    exact (canonical1754 hH).trans (sound1467 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2960 (2 : Fin 5)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2960 (2 : Fin 5) = raw1826 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2960 raw1826; decide +kernel
    rw [heq]
    exact (canonical1826 hH).trans (sound1031 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2960 (3 : Fin 5)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2960 (3 : Fin 5) = raw1837 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2960 raw1837; decide +kernel
    rw [heq]
    exact (canonical1837 hH).trans (sound1031 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2960 (4 : Fin 5)) =
      Sparse.eval value1667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2960 (4 : Fin 5) = raw1839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2960 raw1839; decide +kernel
    rw [heq]
    exact (canonical1839 hH).trans (sound1667 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2960 + (injectiveMoment H (mergeFirst pivotMatrix2960 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2960 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2960 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2960 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2960 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2960, value1031, value1467, value1494, value1667, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2961 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2961 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound2961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2961 = Sparse.eval value2961 (momentVector H) := by
  have heq : pivotMatrix2961 = (fun u v => node2961 (pivotPermutation2961 u) v) := by apply Matrix.ext; unfold pivotMatrix2961 node2961 pivotPermutation2961; decide +kernel
  have hmoment : injectiveMoment H node2961 = injectiveMoment H pivotMatrix2961 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2961 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2961 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2961 (0 : Fin 5)) =
      Sparse.eval value1497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2961 (0 : Fin 5) = raw1183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2961 raw1183; decide +kernel
    rw [heq]
    exact (canonical1183 hH).trans (sound1497 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2961 (1 : Fin 5)) =
      Sparse.eval value1605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2961 (1 : Fin 5) = raw1755 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2961 raw1755; decide +kernel
    rw [heq]
    exact (canonical1755 hH).trans (sound1605 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2961 (2 : Fin 5)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2961 (2 : Fin 5) = raw1828 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2961 raw1828; decide +kernel
    rw [heq]
    exact (canonical1828 hH).trans (sound1042 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2961 (3 : Fin 5)) =
      Sparse.eval value1563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2961 (3 : Fin 5) = raw1841 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2961 raw1841; decide +kernel
    rw [heq]
    exact (canonical1841 hH).trans (sound1563 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2961 (4 : Fin 5)) =
      Sparse.eval value2417 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2961 (4 : Fin 5) = raw1842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2961 raw1842; decide +kernel
    rw [heq]
    exact (canonical1842 hH).trans (sound2417 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2961 + (injectiveMoment H (mergeFirst pivotMatrix2961 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2961 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2961 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2961 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2961 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2961, value1042, value1497, value1563, value1605, value2417, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2962 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2962 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2962 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2962 = Sparse.eval value2962 (momentVector H) := by
  have heq : pivotMatrix2962 = (fun u v => node2962 (pivotPermutation2962 u) v) := by apply Matrix.ext; unfold pivotMatrix2962 node2962 pivotPermutation2962; decide +kernel
  have hmoment : injectiveMoment H node2962 = injectiveMoment H pivotMatrix2962 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2962 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2962 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2962 (0 : Fin 5)) =
      Sparse.eval value1495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2962 (0 : Fin 5) = raw1196 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2962 raw1196; decide +kernel
    rw [heq]
    exact (canonical1196 hH).trans (sound1495 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2962 (1 : Fin 5)) =
      Sparse.eval value2418 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2962 (1 : Fin 5) = raw1757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2962 raw1757; decide +kernel
    rw [heq]
    exact (canonical1757 hH).trans (sound2418 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2962 (2 : Fin 5)) =
      Sparse.eval value2415 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2962 (2 : Fin 5) = raw1847 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2962 raw1847; decide +kernel
    rw [heq]
    exact (canonical1847 hH).trans (sound2415 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2962 (3 : Fin 5)) =
      Sparse.eval value2416 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2962 (3 : Fin 5) = raw1853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2962 raw1853; decide +kernel
    rw [heq]
    exact (canonical1853 hH).trans (sound2416 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2962 (4 : Fin 5)) =
      Sparse.eval value1671 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2962 (4 : Fin 5) = raw1855 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2962 raw1855; decide +kernel
    rw [heq]
    exact (canonical1855 hH).trans (sound1671 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2962 + (injectiveMoment H (mergeFirst pivotMatrix2962 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2962 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2962 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2962 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2962 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2962, value1495, value1671, value2415, value2416, value2418, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2963 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2963 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2963 = Sparse.eval value2963 (momentVector H) := by
  have heq : pivotMatrix2963 = (fun u v => node2963 (pivotPermutation2963 u) v) := by apply Matrix.ext; unfold pivotMatrix2963 node2963 pivotPermutation2963; decide +kernel
  have hmoment : injectiveMoment H node2963 = injectiveMoment H pivotMatrix2963 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2963 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2963 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2963 (0 : Fin 5)) =
      Sparse.eval value1494 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2963 (0 : Fin 5) = raw1198 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2963 raw1198; decide +kernel
    rw [heq]
    exact (canonical1198 hH).trans (sound1494 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2963 (1 : Fin 5)) =
      Sparse.eval value1484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2963 (1 : Fin 5) = raw1759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2963 raw1759; decide +kernel
    rw [heq]
    exact (canonical1759 hH).trans (sound1484 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2963 (2 : Fin 5)) =
      Sparse.eval value2414 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2963 (2 : Fin 5) = raw1850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2963 raw1850; decide +kernel
    rw [heq]
    exact (canonical1850 hH).trans (sound2414 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2963 (3 : Fin 5)) =
      Sparse.eval value1486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2963 (3 : Fin 5) = raw1857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2963 raw1857; decide +kernel
    rw [heq]
    exact (canonical1857 hH).trans (sound1486 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2963 (4 : Fin 5)) =
      Sparse.eval value1486 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2963 (4 : Fin 5) = raw1858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2963 raw1858; decide +kernel
    rw [heq]
    exact (canonical1858 hH).trans (sound1486 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2963 + (injectiveMoment H (mergeFirst pivotMatrix2963 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2963 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2963 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2963 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2963 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2963, value1484, value1486, value1494, value2414, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2964 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2964 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem sound2964 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2964 = Sparse.eval value2964 (momentVector H) := by
  have heq : pivotMatrix2964 = (fun u v => node2964 (pivotPermutation2964 u) v) := by apply Matrix.ext; unfold pivotMatrix2964 node2964 pivotPermutation2964; decide +kernel
  have hmoment : injectiveMoment H node2964 = injectiveMoment H pivotMatrix2964 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2964 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2964 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2964 (0 : Fin 5)) =
      Sparse.eval value1503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2964 (0 : Fin 5) = raw1207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2964 raw1207; decide +kernel
    rw [heq]
    exact (canonical1207 hH).trans (sound1503 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2964 (1 : Fin 5)) =
      Sparse.eval value1646 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2964 (1 : Fin 5) = raw1772 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2964 raw1772; decide +kernel
    rw [heq]
    exact (canonical1772 hH).trans (sound1646 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2964 (2 : Fin 5)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2964 (2 : Fin 5) = raw1874 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2964 raw1874; decide +kernel
    rw [heq]
    exact (canonical1874 hH).trans (sound1221 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2964 (3 : Fin 5)) =
      Sparse.eval value1221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2964 (3 : Fin 5) = raw1894 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2964 raw1894; decide +kernel
    rw [heq]
    exact (canonical1894 hH).trans (sound1221 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2964 (4 : Fin 5)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2964 (4 : Fin 5) = raw1895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2964 raw1895; decide +kernel
    rw [heq]
    exact (canonical1895 hH).trans (sound1680 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2964 + (injectiveMoment H (mergeFirst pivotMatrix2964 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2964 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2964 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2964 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2964 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2964, value1221, value1503, value1646, value1680, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2965 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2965 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound2965 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2965 = Sparse.eval value2965 (momentVector H) := by
  have heq : pivotMatrix2965 = (fun u v => node2965 (pivotPermutation2965 u) v) := by apply Matrix.ext; unfold pivotMatrix2965 node2965 pivotPermutation2965; decide +kernel
  have hmoment : injectiveMoment H node2965 = injectiveMoment H pivotMatrix2965 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2965 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2965 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2965 (0 : Fin 5)) =
      Sparse.eval value1506 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2965 (0 : Fin 5) = raw1210 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2965 raw1210; decide +kernel
    rw [heq]
    exact (canonical1210 hH).trans (sound1506 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2965 (1 : Fin 5)) =
      Sparse.eval value1649 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2965 (1 : Fin 5) = raw1775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2965 raw1775; decide +kernel
    rw [heq]
    exact (canonical1775 hH).trans (sound1649 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2965 (2 : Fin 5)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2965 (2 : Fin 5) = raw1876 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2965 raw1876; decide +kernel
    rw [heq]
    exact (canonical1876 hH).trans (sound969 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2965 (3 : Fin 5)) =
      Sparse.eval value1683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2965 (3 : Fin 5) = raw1900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2965 raw1900; decide +kernel
    rw [heq]
    exact (canonical1900 hH).trans (sound1683 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2965 (4 : Fin 5)) =
      Sparse.eval value2708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2965 (4 : Fin 5) = raw1901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2965 raw1901; decide +kernel
    rw [heq]
    exact (canonical1901 hH).trans (sound2708 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2965 + (injectiveMoment H (mergeFirst pivotMatrix2965 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2965 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2965 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2965 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2965 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2965, value1506, value1649, value1683, value2708, value969, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2966 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2966 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem sound2966 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2966 = Sparse.eval value2966 (momentVector H) := by
  have heq : pivotMatrix2966 = (fun u v => node2966 (pivotPermutation2966 u) v) := by apply Matrix.ext; unfold pivotMatrix2966 node2966 pivotPermutation2966; decide +kernel
  have hmoment : injectiveMoment H node2966 = injectiveMoment H pivotMatrix2966 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2966 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2966 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2966 (0 : Fin 5)) =
      Sparse.eval value1507 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2966 (0 : Fin 5) = raw1213 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2966 raw1213; decide +kernel
    rw [heq]
    exact (canonical1213 hH).trans (sound1507 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2966 (1 : Fin 5)) =
      Sparse.eval value1650 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2966 (1 : Fin 5) = raw1778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2966 raw1778; decide +kernel
    rw [heq]
    exact (canonical1778 hH).trans (sound1650 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2966 (2 : Fin 5)) =
      Sparse.eval value2421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2966 (2 : Fin 5) = raw1881 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2966 raw1881; decide +kernel
    rw [heq]
    exact (canonical1881 hH).trans (sound2421 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2966 (3 : Fin 5)) =
      Sparse.eval value2421 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2966 (3 : Fin 5) = raw1903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2966 raw1903; decide +kernel
    rw [heq]
    exact (canonical1903 hH).trans (sound2421 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2966 (4 : Fin 5)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2966 (4 : Fin 5) = raw1905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2966 raw1905; decide +kernel
    rw [heq]
    exact (canonical1905 hH).trans (sound2676 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2966 + (injectiveMoment H (mergeFirst pivotMatrix2966 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2966 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2966 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2966 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2966 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2966, value1507, value1650, value2421, value2676, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2967 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2967 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem sound2967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2967 = Sparse.eval value2967 (momentVector H) := by
  have heq : pivotMatrix2967 = (fun u v => node2967 (pivotPermutation2967 u) v) := by apply Matrix.ext; unfold pivotMatrix2967 node2967 pivotPermutation2967; decide +kernel
  have hmoment : injectiveMoment H node2967 = injectiveMoment H pivotMatrix2967 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2967 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2967 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2967 (0 : Fin 5)) =
      Sparse.eval value1506 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2967 (0 : Fin 5) = raw1214 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2967 raw1214; decide +kernel
    rw [heq]
    exact (canonical1214 hH).trans (sound1506 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2967 (1 : Fin 5)) =
      Sparse.eval value1652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2967 (1 : Fin 5) = raw1780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2967 raw1780; decide +kernel
    rw [heq]
    exact (canonical1780 hH).trans (sound1652 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2967 (2 : Fin 5)) =
      Sparse.eval value2419 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2967 (2 : Fin 5) = raw1885 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2967 raw1885; decide +kernel
    rw [heq]
    exact (canonical1885 hH).trans (sound2419 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2967 (3 : Fin 5)) =
      Sparse.eval value2767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2967 (3 : Fin 5) = raw1908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2967 raw1908; decide +kernel
    rw [heq]
    exact (canonical1908 hH).trans (sound2767 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2967 (4 : Fin 5)) =
      Sparse.eval value2704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2967 (4 : Fin 5) = raw1910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2967 raw1910; decide +kernel
    rw [heq]
    exact (canonical1910 hH).trans (sound2704 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2967 + (injectiveMoment H (mergeFirst pivotMatrix2967 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2967 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2967 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2967 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2967 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2967, value1506, value1652, value2419, value2704, value2767, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2968 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2968 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem sound2968 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2968 = Sparse.eval value2968 (momentVector H) := by
  have heq : pivotMatrix2968 = (fun u v => node2968 (pivotPermutation2968 u) v) := by apply Matrix.ext; unfold pivotMatrix2968 node2968 pivotPermutation2968; decide +kernel
  have hmoment : injectiveMoment H node2968 = injectiveMoment H pivotMatrix2968 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2968 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2968 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2968 (0 : Fin 5)) =
      Sparse.eval value1508 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2968 (0 : Fin 5) = raw1215 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2968 raw1215; decide +kernel
    rw [heq]
    exact (canonical1215 hH).trans (sound1508 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2968 (1 : Fin 5)) =
      Sparse.eval value1653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2968 (1 : Fin 5) = raw1781 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2968 raw1781; decide +kernel
    rw [heq]
    exact (canonical1781 hH).trans (sound1653 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2968 (2 : Fin 5)) =
      Sparse.eval value2420 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2968 (2 : Fin 5) = raw1886 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2968 raw1886; decide +kernel
    rw [heq]
    exact (canonical1886 hH).trans (sound2420 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2968 (3 : Fin 5)) =
      Sparse.eval value1685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2968 (3 : Fin 5) = raw1909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2968 raw1909; decide +kernel
    rw [heq]
    exact (canonical1909 hH).trans (sound1685 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2968 (4 : Fin 5)) =
      Sparse.eval value2704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2968 (4 : Fin 5) = raw1911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2968 raw1911; decide +kernel
    rw [heq]
    exact (canonical1911 hH).trans (sound2704 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2968 + (injectiveMoment H (mergeFirst pivotMatrix2968 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2968 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2968 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2968 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2968 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2968, value1508, value1653, value1685, value2420, value2704, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2969 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2969 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2969 = Sparse.eval value2969 (momentVector H) := by
  have heq : pivotMatrix2969 = (fun u v => node2969 (pivotPermutation2969 u) v) := by apply Matrix.ext; unfold pivotMatrix2969 node2969 pivotPermutation2969; decide +kernel
  have hmoment : injectiveMoment H node2969 = injectiveMoment H pivotMatrix2969 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2969 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2969 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2969 (0 : Fin 5)) =
      Sparse.eval value1504 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2969 (0 : Fin 5) = raw1219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2969 raw1219; decide +kernel
    rw [heq]
    exact (canonical1219 hH).trans (sound1504 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2969 (1 : Fin 5)) =
      Sparse.eval value1655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2969 (1 : Fin 5) = raw1787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2969 raw1787; decide +kernel
    rw [heq]
    exact (canonical1787 hH).trans (sound1655 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2969 (2 : Fin 5)) =
      Sparse.eval value2704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2969 (2 : Fin 5) = raw1910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2969 raw1910; decide +kernel
    rw [heq]
    exact (canonical1910 hH).trans (sound2704 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2969 (3 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2969 (3 : Fin 5) = raw1921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2969 raw1921; decide +kernel
    rw [heq]
    exact (canonical1921 hH).trans (sound2750 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2969 (4 : Fin 5)) =
      Sparse.eval value1690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2969 (4 : Fin 5) = raw1923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2969 raw1923; decide +kernel
    rw [heq]
    exact (canonical1923 hH).trans (sound1690 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2969 + (injectiveMoment H (mergeFirst pivotMatrix2969 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2969 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2969 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2969 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2969 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2969, value1504, value1655, value1690, value2704, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2970 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2970 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2970 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2970 = Sparse.eval value2970 (momentVector H) := by
  have heq : pivotMatrix2970 = (fun u v => node2970 (pivotPermutation2970 u) v) := by apply Matrix.ext; unfold pivotMatrix2970 node2970 pivotPermutation2970; decide +kernel
  have hmoment : injectiveMoment H node2970 = injectiveMoment H pivotMatrix2970 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2970 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2970 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2970 (0 : Fin 5)) =
      Sparse.eval value1503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2970 (0 : Fin 5) = raw1221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2970 raw1221; decide +kernel
    rw [heq]
    exact (canonical1221 hH).trans (sound1503 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2970 (1 : Fin 5)) =
      Sparse.eval value1657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2970 (1 : Fin 5) = raw1790 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2970 raw1790; decide +kernel
    rw [heq]
    exact (canonical1790 hH).trans (sound1657 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2970 (2 : Fin 5)) =
      Sparse.eval value2424 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2970 (2 : Fin 5) = raw1915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2970 raw1915; decide +kernel
    rw [heq]
    exact (canonical1915 hH).trans (sound2424 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2970 (3 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2970 (3 : Fin 5) = raw1926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2970 raw1926; decide +kernel
    rw [heq]
    exact (canonical1926 hH).trans (sound2740 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2970 (4 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2970 (4 : Fin 5) = raw1928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2970 raw1928; decide +kernel
    rw [heq]
    exact (canonical1928 hH).trans (sound2740 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2970 + (injectiveMoment H (mergeFirst pivotMatrix2970 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2970 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2970 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2970 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2970 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2970, value1503, value1657, value2424, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2971 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2971 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound2971 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2971 = Sparse.eval value2971 (momentVector H) := by
  have heq : pivotMatrix2971 = (fun u v => node2971 (pivotPermutation2971 u) v) := by apply Matrix.ext; unfold pivotMatrix2971 node2971 pivotPermutation2971; decide +kernel
  have hmoment : injectiveMoment H node2971 = injectiveMoment H pivotMatrix2971 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2971 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2971 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2971 (0 : Fin 5)) =
      Sparse.eval value1512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2971 (0 : Fin 5) = raw1240 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2971 raw1240; decide +kernel
    rw [heq]
    exact (canonical1240 hH).trans (sound1512 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2971 (1 : Fin 5)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2971 (1 : Fin 5) = raw1864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2971 raw1864; decide +kernel
    rw [heq]
    exact (canonical1864 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2971 (2 : Fin 5)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2971 (2 : Fin 5) = raw2009 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2971 raw2009; decide +kernel
    rw [heq]
    exact (canonical2009 hH).trans (sound1202 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2971 (3 : Fin 5)) =
      Sparse.eval value1715 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2971 (3 : Fin 5) = raw2018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2971 raw2018; decide +kernel
    rw [heq]
    exact (canonical2018 hH).trans (sound1715 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2971 (4 : Fin 5)) =
      Sparse.eval value1716 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2971 (4 : Fin 5) = raw2022 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2971 raw2022; decide +kernel
    rw [heq]
    exact (canonical2022 hH).trans (sound1716 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2971 + (injectiveMoment H (mergeFirst pivotMatrix2971 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2971 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2971 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2971 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2971 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2971, value1202, value1512, value1715, value1716, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2972 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2972 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound2972 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2972 = Sparse.eval value2972 (momentVector H) := by
  have heq : pivotMatrix2972 = (fun u v => node2972 (pivotPermutation2972 u) v) := by apply Matrix.ext; unfold pivotMatrix2972 node2972 pivotPermutation2972; decide +kernel
  have hmoment : injectiveMoment H node2972 = injectiveMoment H pivotMatrix2972 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2972 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2972 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2972 (0 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2972 (0 : Fin 5) = raw1243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2972 raw1243; decide +kernel
    rw [heq]
    exact (canonical1243 hH).trans (sound1513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2972 (1 : Fin 5)) =
      Sparse.eval value1203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2972 (1 : Fin 5) = raw1865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2972 raw1865; decide +kernel
    rw [heq]
    exact (canonical1865 hH).trans (sound1203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2972 (2 : Fin 5)) =
      Sparse.eval value2425 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2972 (2 : Fin 5) = raw2010 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2972 raw2010; decide +kernel
    rw [heq]
    exact (canonical2010 hH).trans (sound2425 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2972 (3 : Fin 5)) =
      Sparse.eval value2580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2972 (3 : Fin 5) = raw2025 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2972 raw2025; decide +kernel
    rw [heq]
    exact (canonical2025 hH).trans (sound2580 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2972 (4 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2972 (4 : Fin 5) = raw2028 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2972 raw2028; decide +kernel
    rw [heq]
    exact (canonical2028 hH).trans (sound1718 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2972 + (injectiveMoment H (mergeFirst pivotMatrix2972 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2972 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2972 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2972 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2972 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2972, value1203, value1513, value1718, value2425, value2580, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2973 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2973 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2973 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2973 = Sparse.eval value2973 (momentVector H) := by
  have heq : pivotMatrix2973 = (fun u v => node2973 (pivotPermutation2973 u) v) := by apply Matrix.ext; unfold pivotMatrix2973 node2973 pivotPermutation2973; decide +kernel
  have hmoment : injectiveMoment H node2973 = injectiveMoment H pivotMatrix2973 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2973 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2973 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2973 (0 : Fin 5)) =
      Sparse.eval value1513 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2973 (0 : Fin 5) = raw1246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2973 raw1246; decide +kernel
    rw [heq]
    exact (canonical1246 hH).trans (sound1513 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2973 (1 : Fin 5)) =
      Sparse.eval value1043 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2973 (1 : Fin 5) = raw1866 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2973 raw1866; decide +kernel
    rw [heq]
    exact (canonical1866 hH).trans (sound1043 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2973 (2 : Fin 5)) =
      Sparse.eval value2428 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2973 (2 : Fin 5) = raw2011 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2973 raw2011; decide +kernel
    rw [heq]
    exact (canonical2011 hH).trans (sound2428 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2973 (3 : Fin 5)) =
      Sparse.eval value2605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2973 (3 : Fin 5) = raw2030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2973 raw2030; decide +kernel
    rw [heq]
    exact (canonical2030 hH).trans (sound2605 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2973 (4 : Fin 5)) =
      Sparse.eval value1719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2973 (4 : Fin 5) = raw2032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2973 raw2032; decide +kernel
    rw [heq]
    exact (canonical2032 hH).trans (sound1719 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2973 + (injectiveMoment H (mergeFirst pivotMatrix2973 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2973 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2973 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2973 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2973 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2973, value1043, value1513, value1719, value2428, value2605, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2974 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2974 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2974 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2974 = Sparse.eval value2974 (momentVector H) := by
  have heq : pivotMatrix2974 = (fun u v => node2974 (pivotPermutation2974 u) v) := by apply Matrix.ext; unfold pivotMatrix2974 node2974 pivotPermutation2974; decide +kernel
  have hmoment : injectiveMoment H node2974 = injectiveMoment H pivotMatrix2974 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2974 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2974 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2974 (0 : Fin 5)) =
      Sparse.eval value1512 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2974 (0 : Fin 5) = raw1258 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2974 raw1258; decide +kernel
    rw [heq]
    exact (canonical1258 hH).trans (sound1512 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2974 (1 : Fin 5)) =
      Sparse.eval value2424 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2974 (1 : Fin 5) = raw1915 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2974 raw1915; decide +kernel
    rw [heq]
    exact (canonical1915 hH).trans (sound2424 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2974 (2 : Fin 5)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2974 (2 : Fin 5) = raw2052 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2974 raw2052; decide +kernel
    rw [heq]
    exact (canonical2052 hH).trans (sound2427 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2974 (3 : Fin 5)) =
      Sparse.eval value2579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2974 (3 : Fin 5) = raw2061 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2974 raw2061; decide +kernel
    rw [heq]
    exact (canonical2061 hH).trans (sound2579 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2974 (4 : Fin 5)) =
      Sparse.eval value2579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2974 (4 : Fin 5) = raw2062 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2974 raw2062; decide +kernel
    rw [heq]
    exact (canonical2062 hH).trans (sound2579 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2974 + (injectiveMoment H (mergeFirst pivotMatrix2974 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2974 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2974 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2974 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2974 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2974, value1512, value2424, value2427, value2579, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2975 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2975 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2975 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2975 = Sparse.eval value2975 (momentVector H) := by
  have heq : pivotMatrix2975 = (fun u v => node2975 (pivotPermutation2975 u) v) := by apply Matrix.ext; unfold pivotMatrix2975 node2975 pivotPermutation2975; decide +kernel
  have hmoment : injectiveMoment H node2975 = injectiveMoment H pivotMatrix2975 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2975 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2975 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2975 (0 : Fin 5)) =
      Sparse.eval value2824 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2975 (0 : Fin 5) = raw3410 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2975 raw3410; decide +kernel
    rw [heq]
    exact (canonical3410 hH).trans (sound2824 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2975 (1 : Fin 5)) =
      Sparse.eval value2429 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2975 (1 : Fin 5) = raw1948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2975 raw1948; decide +kernel
    rw [heq]
    exact (canonical1948 hH).trans (sound2429 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2975 (2 : Fin 5)) =
      Sparse.eval value1654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2975 (2 : Fin 5) = raw1785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2975 raw1785; decide +kernel
    rw [heq]
    exact (canonical1785 hH).trans (sound1654 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2975 (3 : Fin 5)) =
      Sparse.eval value1645 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2975 (3 : Fin 5) = raw1770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2975 raw1770; decide +kernel
    rw [heq]
    exact (canonical1770 hH).trans (sound1645 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2975 (4 : Fin 5)) =
      Sparse.eval value1645 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2975 (4 : Fin 5) = raw1769 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2975 raw1769; decide +kernel
    rw [heq]
    exact (canonical1769 hH).trans (sound1645 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2975 + (injectiveMoment H (mergeFirst pivotMatrix2975 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2975 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2975 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2975 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2975 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2975, value1645, value1654, value2429, value2824, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2976 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2976 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem sound2976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2976 = Sparse.eval value2976 (momentVector H) := by
  have heq : pivotMatrix2976 = (fun u v => node2976 (pivotPermutation2976 u) v) := by apply Matrix.ext; unfold pivotMatrix2976 node2976 pivotPermutation2976; decide +kernel
  have hmoment : injectiveMoment H node2976 = injectiveMoment H pivotMatrix2976 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2976 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2976 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2976 (0 : Fin 5)) =
      Sparse.eval value2812 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2976 (0 : Fin 5) = raw3071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2976 raw3071; decide +kernel
    rw [heq]
    exact (canonical3071 hH).trans (sound2812 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2976 (1 : Fin 5)) =
      Sparse.eval value2708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2976 (1 : Fin 5) = raw1901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2976 raw1901; decide +kernel
    rw [heq]
    exact (canonical1901 hH).trans (sound2708 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2976 (2 : Fin 5)) =
      Sparse.eval value1654 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2976 (2 : Fin 5) = raw1785 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2976 raw1785; decide +kernel
    rw [heq]
    exact (canonical1785 hH).trans (sound1654 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2976 (3 : Fin 5)) =
      Sparse.eval value1649 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2976 (3 : Fin 5) = raw1776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2976 raw1776; decide +kernel
    rw [heq]
    exact (canonical1776 hH).trans (sound1649 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2976 (4 : Fin 5)) =
      Sparse.eval value1649 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2976 (4 : Fin 5) = raw1775 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2976 raw1775; decide +kernel
    rw [heq]
    exact (canonical1775 hH).trans (sound1649 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2976 + (injectiveMoment H (mergeFirst pivotMatrix2976 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2976 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2976 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2976 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2976 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2976, value1649, value1654, value2708, value2812, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2977 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2977 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound2977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2977 = Sparse.eval value2977 (momentVector H) := by
  have heq : pivotMatrix2977 = (fun u v => node2977 (pivotPermutation2977 u) v) := by apply Matrix.ext; unfold pivotMatrix2977 node2977 pivotPermutation2977; decide +kernel
  have hmoment : injectiveMoment H node2977 = injectiveMoment H pivotMatrix2977 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2977 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2977 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2977 (0 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2977 (0 : Fin 5) = raw3073 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2977 raw3073; decide +kernel
    rw [heq]
    exact (canonical3073 hH).trans (sound2750 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2977 (1 : Fin 5)) =
      Sparse.eval value2704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2977 (1 : Fin 5) = raw1910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2977 raw1910; decide +kernel
    rw [heq]
    exact (canonical1910 hH).trans (sound2704 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2977 (2 : Fin 5)) =
      Sparse.eval value1655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2977 (2 : Fin 5) = raw1787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2977 raw1787; decide +kernel
    rw [heq]
    exact (canonical1787 hH).trans (sound1655 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2977 (3 : Fin 5)) =
      Sparse.eval value1653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2977 (3 : Fin 5) = raw1782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2977 raw1782; decide +kernel
    rw [heq]
    exact (canonical1782 hH).trans (sound1653 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2977 (4 : Fin 5)) =
      Sparse.eval value1652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2977 (4 : Fin 5) = raw1780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2977 raw1780; decide +kernel
    rw [heq]
    exact (canonical1780 hH).trans (sound1652 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2977 + (injectiveMoment H (mergeFirst pivotMatrix2977 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2977 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2977 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2977 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2977 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2977, value1652, value1653, value1655, value2704, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2978 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2978 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem sound2978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2978 = Sparse.eval value2978 (momentVector H) := by
  have heq : pivotMatrix2978 = (fun u v => node2978 (pivotPermutation2978 u) v) := by apply Matrix.ext; unfold pivotMatrix2978 node2978 pivotPermutation2978; decide +kernel
  have hmoment : injectiveMoment H node2978 = injectiveMoment H pivotMatrix2978 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2978 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2978 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2978 (0 : Fin 5)) =
      Sparse.eval value2752 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2978 (0 : Fin 5) = raw3413 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2978 raw3413; decide +kernel
    rw [heq]
    exact (canonical3413 hH).trans (sound2752 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2978 (1 : Fin 5)) =
      Sparse.eval value2426 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2978 (1 : Fin 5) = raw1962 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2978 raw1962; decide +kernel
    rw [heq]
    exact (canonical1962 hH).trans (sound2426 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2978 (2 : Fin 5)) =
      Sparse.eval value1656 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2978 (2 : Fin 5) = raw1789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2978 raw1789; decide +kernel
    rw [heq]
    exact (canonical1789 hH).trans (sound1656 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2978 (3 : Fin 5)) =
      Sparse.eval value1653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2978 (3 : Fin 5) = raw1782 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2978 raw1782; decide +kernel
    rw [heq]
    exact (canonical1782 hH).trans (sound1653 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2978 (4 : Fin 5)) =
      Sparse.eval value1651 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2978 (4 : Fin 5) = raw1779 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2978 raw1779; decide +kernel
    rw [heq]
    exact (canonical1779 hH).trans (sound1651 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2978 + (injectiveMoment H (mergeFirst pivotMatrix2978 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2978 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2978 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2978 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2978 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2978, value1651, value1653, value1656, value2426, value2752, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2979 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2979 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem sound2979 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2979 = Sparse.eval value2979 (momentVector H) := by
  have heq : pivotMatrix2979 = (fun u v => node2979 (pivotPermutation2979 u) v) := by apply Matrix.ext; unfold pivotMatrix2979 node2979 pivotPermutation2979; decide +kernel
  have hmoment : injectiveMoment H node2979 = injectiveMoment H pivotMatrix2979 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2979 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2979 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2979 (0 : Fin 5)) =
      Sparse.eval value2609 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2979 (0 : Fin 5) = raw3414 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2979 raw3414; decide +kernel
    rw [heq]
    exact (canonical3414 hH).trans (sound2609 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2979 (1 : Fin 5)) =
      Sparse.eval value2427 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2979 (1 : Fin 5) = raw1963 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2979 raw1963; decide +kernel
    rw [heq]
    exact (canonical1963 hH).trans (sound2427 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2979 (2 : Fin 5)) =
      Sparse.eval value1657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2979 (2 : Fin 5) = raw1790 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2979 raw1790; decide +kernel
    rw [heq]
    exact (canonical1790 hH).trans (sound1657 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2979 (3 : Fin 5)) =
      Sparse.eval value1652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2979 (3 : Fin 5) = raw1783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2979 raw1783; decide +kernel
    rw [heq]
    exact (canonical1783 hH).trans (sound1652 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2979 (4 : Fin 5)) =
      Sparse.eval value1652 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2979 (4 : Fin 5) = raw1780 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2979 raw1780; decide +kernel
    rw [heq]
    exact (canonical1780 hH).trans (sound1652 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2979 + (injectiveMoment H (mergeFirst pivotMatrix2979 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2979 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2979 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2979 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2979 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2979, value1652, value1657, value2427, value2609, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2980 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2980 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

theorem sound2980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2980 = Sparse.eval value2980 (momentVector H) := by
  have heq : pivotMatrix2980 = (fun u v => node2980 (pivotPermutation2980 u) v) := by apply Matrix.ext; unfold pivotMatrix2980 node2980 pivotPermutation2980; decide +kernel
  have hmoment : injectiveMoment H node2980 = injectiveMoment H pivotMatrix2980 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2980 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2980 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2980 (0 : Fin 5)) =
      Sparse.eval value1666 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2980 (0 : Fin 5) = raw2207 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2980 raw2207; decide +kernel
    rw [heq]
    exact (canonical2207 hH).trans (sound1666 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2980 (1 : Fin 5)) =
      Sparse.eval value2738 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2980 (1 : Fin 5) = raw1833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2980 raw1833; decide +kernel
    rw [heq]
    exact (canonical1833 hH).trans (sound2738 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2980 (2 : Fin 5)) =
      Sparse.eval value1659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2980 (2 : Fin 5) = raw1803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2980 raw1803; decide +kernel
    rw [heq]
    exact (canonical1803 hH).trans (sound1659 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2980 (3 : Fin 5)) =
      Sparse.eval value1658 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2980 (3 : Fin 5) = raw1802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2980 raw1802; decide +kernel
    rw [heq]
    exact (canonical1802 hH).trans (sound1658 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2980 (4 : Fin 5)) =
      Sparse.eval value1547 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2980 (4 : Fin 5) = raw1801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2980 raw1801; decide +kernel
    rw [heq]
    exact (canonical1801 hH).trans (sound1547 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2980 + (injectiveMoment H (mergeFirst pivotMatrix2980 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2980 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2980 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2980 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2980 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2980, value1547, value1658, value1659, value1666, value2738, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2981 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2981 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem sound2981 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2981 = Sparse.eval value2981 (momentVector H) := by
  have heq : pivotMatrix2981 = (fun u v => node2981 (pivotPermutation2981 u) v) := by apply Matrix.ext; unfold pivotMatrix2981 node2981 pivotPermutation2981; decide +kernel
  have hmoment : injectiveMoment H node2981 = injectiveMoment H pivotMatrix2981 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2981 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2981 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2981 (0 : Fin 5)) =
      Sparse.eval value1756 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2981 (0 : Fin 5) = raw2211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2981 raw2211; decide +kernel
    rw [heq]
    exact (canonical2211 hH).trans (sound1756 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2981 (1 : Fin 5)) =
      Sparse.eval value2436 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2981 (1 : Fin 5) = raw1843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2981 raw1843; decide +kernel
    rw [heq]
    exact (canonical1843 hH).trans (sound2436 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2981 (2 : Fin 5)) =
      Sparse.eval value1660 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2981 (2 : Fin 5) = raw1809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2981 raw1809; decide +kernel
    rw [heq]
    exact (canonical1809 hH).trans (sound1660 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2981 (3 : Fin 5)) =
      Sparse.eval value1660 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2981 (3 : Fin 5) = raw1806 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2981 raw1806; decide +kernel
    rw [heq]
    exact (canonical1806 hH).trans (sound1660 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2981 (4 : Fin 5)) =
      Sparse.eval value1491 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2981 (4 : Fin 5) = raw1805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2981 raw1805; decide +kernel
    rw [heq]
    exact (canonical1805 hH).trans (sound1491 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2981 + (injectiveMoment H (mergeFirst pivotMatrix2981 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2981 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2981 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2981 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2981 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2981, value1491, value1660, value1756, value2436, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2982 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2982 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound2982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2982 = Sparse.eval value2982 (momentVector H) := by
  have heq : pivotMatrix2982 = (fun u v => node2982 (pivotPermutation2982 u) v) := by apply Matrix.ext; unfold pivotMatrix2982 node2982 pivotPermutation2982; decide +kernel
  have hmoment : injectiveMoment H node2982 = injectiveMoment H pivotMatrix2982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2982 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2982 (0 : Fin 5)) =
      Sparse.eval value2762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (0 : Fin 5) = raw3433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw3433; decide +kernel
    rw [heq]
    exact (canonical3433 hH).trans (sound2762 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2982 (1 : Fin 5)) =
      Sparse.eval value1710 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (1 : Fin 5) = raw1989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1989; decide +kernel
    rw [heq]
    exact (canonical1989 hH).trans (sound1710 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2982 (2 : Fin 5)) =
      Sparse.eval value1662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (2 : Fin 5) = raw1812 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1812; decide +kernel
    rw [heq]
    exact (canonical1812 hH).trans (sound1662 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2982 (3 : Fin 5)) =
      Sparse.eval value2406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (3 : Fin 5) = raw1808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1808; decide +kernel
    rw [heq]
    exact (canonical1808 hH).trans (sound2406 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2982 (4 : Fin 5)) =
      Sparse.eval value1661 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2982 (4 : Fin 5) = raw1807 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2982 raw1807; decide +kernel
    rw [heq]
    exact (canonical1807 hH).trans (sound1661 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2982 + (injectiveMoment H (mergeFirst pivotMatrix2982 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2982 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2982, value1661, value1662, value1710, value2406, value2762, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2983 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2983 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

theorem sound2983 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2983 = Sparse.eval value2983 (momentVector H) := by
  have heq : pivotMatrix2983 = (fun u v => node2983 (pivotPermutation2983 u) v) := by apply Matrix.ext; unfold pivotMatrix2983 node2983 pivotPermutation2983; decide +kernel
  have hmoment : injectiveMoment H node2983 = injectiveMoment H pivotMatrix2983 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2983 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2983 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2983 (0 : Fin 5)) =
      Sparse.eval value1545 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2983 (0 : Fin 5) = raw1520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2983 raw1520; decide +kernel
    rw [heq]
    exact (canonical1520 hH).trans (sound1545 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2983 (1 : Fin 5)) =
      Sparse.eval value1658 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2983 (1 : Fin 5) = raw1802 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2983 raw1802; decide +kernel
    rw [heq]
    exact (canonical1802 hH).trans (sound1658 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2983 (2 : Fin 5)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2983 (2 : Fin 5) = raw1827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2983 raw1827; decide +kernel
    rw [heq]
    exact (canonical1827 hH).trans (sound1094 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2983 (3 : Fin 5)) =
      Sparse.eval value2738 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2983 (3 : Fin 5) = raw1833 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2983 raw1833; decide +kernel
    rw [heq]
    exact (canonical1833 hH).trans (sound2738 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2983 (4 : Fin 5)) =
      Sparse.eval value1665 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2983 (4 : Fin 5) = raw1834 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2983 raw1834; decide +kernel
    rw [heq]
    exact (canonical1834 hH).trans (sound1665 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2983 + (injectiveMoment H (mergeFirst pivotMatrix2983 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2983 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2983 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2983 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2983 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2983, value1094, value1545, value1658, value1665, value2738, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2984 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2984 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem sound2984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2984 = Sparse.eval value2984 (momentVector H) := by
  have heq : pivotMatrix2984 = (fun u v => node2984 (pivotPermutation2984 u) v) := by apply Matrix.ext; unfold pivotMatrix2984 node2984 pivotPermutation2984; decide +kernel
  have hmoment : injectiveMoment H node2984 = injectiveMoment H pivotMatrix2984 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2984 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2984 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2984 (0 : Fin 5)) =
      Sparse.eval value1546 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2984 (0 : Fin 5) = raw1522 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2984 raw1522; decide +kernel
    rw [heq]
    exact (canonical1522 hH).trans (sound1546 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2984 (1 : Fin 5)) =
      Sparse.eval value1663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2984 (1 : Fin 5) = raw1814 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2984 raw1814; decide +kernel
    rw [heq]
    exact (canonical1814 hH).trans (sound1663 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2984 (2 : Fin 5)) =
      Sparse.eval value2626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2984 (2 : Fin 5) = raw1851 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2984 raw1851; decide +kernel
    rw [heq]
    exact (canonical1851 hH).trans (sound2626 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2984 (3 : Fin 5)) =
      Sparse.eval value2416 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2984 (3 : Fin 5) = raw1853 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2984 raw1853; decide +kernel
    rw [heq]
    exact (canonical1853 hH).trans (sound2416 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2984 (4 : Fin 5)) =
      Sparse.eval value1671 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2984 (4 : Fin 5) = raw1854 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2984 raw1854; decide +kernel
    rw [heq]
    exact (canonical1854 hH).trans (sound1671 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2984 + (injectiveMoment H (mergeFirst pivotMatrix2984 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2984 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2984 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2984 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2984 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2984, value1546, value1663, value1671, value2416, value2626, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2985 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2985 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem sound2985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2985 = Sparse.eval value2985 (momentVector H) := by
  have heq : pivotMatrix2985 = (fun u v => node2985 (pivotPermutation2985 u) v) := by apply Matrix.ext; unfold pivotMatrix2985 node2985 pivotPermutation2985; decide +kernel
  have hmoment : injectiveMoment H node2985 = injectiveMoment H pivotMatrix2985 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2985 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2985 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2985 (0 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2985 (0 : Fin 5) = raw1552 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2985 raw1552; decide +kernel
    rw [heq]
    exact (canonical1552 hH).trans (sound1585 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2985 (1 : Fin 5)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2985 (1 : Fin 5) = raw1861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2985 raw1861; decide +kernel
    rw [heq]
    exact (canonical1861 hH).trans (sound1207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2985 (2 : Fin 5)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2985 (2 : Fin 5) = raw1875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2985 raw1875; decide +kernel
    rw [heq]
    exact (canonical1875 hH).trans (sound1207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2985 (3 : Fin 5)) =
      Sparse.eval value1673 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2985 (3 : Fin 5) = raw1883 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2985 raw1883; decide +kernel
    rw [heq]
    exact (canonical1883 hH).trans (sound1673 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2985 (4 : Fin 5)) =
      Sparse.eval value1674 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2985 (4 : Fin 5) = raw1884 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2985 raw1884; decide +kernel
    rw [heq]
    exact (canonical1884 hH).trans (sound1674 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2985 + (injectiveMoment H (mergeFirst pivotMatrix2985 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2985 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2985 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2985 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2985 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2985, value1207, value1585, value1673, value1674, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2986 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2986 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem sound2986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2986 = Sparse.eval value2986 (momentVector H) := by
  have heq : pivotMatrix2986 = (fun u v => node2986 (pivotPermutation2986 u) v) := by apply Matrix.ext; unfold pivotMatrix2986 node2986 pivotPermutation2986; decide +kernel
  have hmoment : injectiveMoment H node2986 = injectiveMoment H pivotMatrix2986 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2986 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2986 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2986 (0 : Fin 5)) =
      Sparse.eval value1548 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2986 (0 : Fin 5) = raw1564 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2986 raw1564; decide +kernel
    rw [heq]
    exact (canonical1564 hH).trans (sound1548 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2986 (1 : Fin 5)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2986 (1 : Fin 5) = raw1862 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2986 raw1862; decide +kernel
    rw [heq]
    exact (canonical1862 hH).trans (sound1109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2986 (2 : Fin 5)) =
      Sparse.eval value1676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2986 (2 : Fin 5) = raw1889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2986 raw1889; decide +kernel
    rw [heq]
    exact (canonical1889 hH).trans (sound1676 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2986 (3 : Fin 5)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2986 (3 : Fin 5) = raw1895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2986 raw1895; decide +kernel
    rw [heq]
    exact (canonical1895 hH).trans (sound1680 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2986 (4 : Fin 5)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2986 (4 : Fin 5) = raw1896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2986 raw1896; decide +kernel
    rw [heq]
    exact (canonical1896 hH).trans (sound2742 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2986 + (injectiveMoment H (mergeFirst pivotMatrix2986 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2986 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2986 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2986 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2986 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2986, value1109, value1548, value1676, value1680, value2742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2987 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2987 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound2987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2987 = Sparse.eval value2987 (momentVector H) := by
  have heq : pivotMatrix2987 = (fun u v => node2987 (pivotPermutation2987 u) v) := by apply Matrix.ext; unfold pivotMatrix2987 node2987 pivotPermutation2987; decide +kernel
  have hmoment : injectiveMoment H node2987 = injectiveMoment H pivotMatrix2987 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2987 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2987 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2987 (0 : Fin 5)) =
      Sparse.eval value1558 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2987 (0 : Fin 5) = raw1566 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2987 raw1566; decide +kernel
    rw [heq]
    exact (canonical1566 hH).trans (sound1558 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2987 (1 : Fin 5)) =
      Sparse.eval value1268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2987 (1 : Fin 5) = raw1863 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2987 raw1863; decide +kernel
    rw [heq]
    exact (canonical1863 hH).trans (sound1268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2987 (2 : Fin 5)) =
      Sparse.eval value1678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2987 (2 : Fin 5) = raw1891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2987 raw1891; decide +kernel
    rw [heq]
    exact (canonical1891 hH).trans (sound1678 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2987 (3 : Fin 5)) =
      Sparse.eval value1682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2987 (3 : Fin 5) = raw1898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2987 raw1898; decide +kernel
    rw [heq]
    exact (canonical1898 hH).trans (sound1682 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2987 (4 : Fin 5)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2987 (4 : Fin 5) = raw1899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2987 raw1899; decide +kernel
    rw [heq]
    exact (canonical1899 hH).trans (sound2748 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2987 + (injectiveMoment H (mergeFirst pivotMatrix2987 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2987 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2987 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2987 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2987 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2987, value1268, value1558, value1678, value1682, value2748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2988 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2988 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2988 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2988 = Sparse.eval value2988 (momentVector H) := by
  have heq : pivotMatrix2988 = (fun u v => node2988 (pivotPermutation2988 u) v) := by apply Matrix.ext; unfold pivotMatrix2988 node2988 pivotPermutation2988; decide +kernel
  have hmoment : injectiveMoment H node2988 = injectiveMoment H pivotMatrix2988 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2988 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2988 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2988 (0 : Fin 5)) =
      Sparse.eval value1614 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2988 (0 : Fin 5) = raw1652 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2988 raw1652; decide +kernel
    rw [heq]
    exact (canonical1652 hH).trans (sound1614 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2988 (1 : Fin 5)) =
      Sparse.eval value1707 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2988 (1 : Fin 5) = raw1984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2988 raw1984; decide +kernel
    rw [heq]
    exact (canonical1984 hH).trans (sound1707 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2988 (2 : Fin 5)) =
      Sparse.eval value1707 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2988 (2 : Fin 5) = raw2014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2988 raw2014; decide +kernel
    rw [heq]
    exact (canonical2014 hH).trans (sound1707 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2988 (3 : Fin 5)) =
      Sparse.eval value1714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2988 (3 : Fin 5) = raw2016 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2988 raw2016; decide +kernel
    rw [heq]
    exact (canonical2016 hH).trans (sound1714 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2988 (4 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2988 (4 : Fin 5) = raw2017 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2988 raw2017; decide +kernel
    rw [heq]
    exact (canonical2017 hH).trans (sound1644 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2988 + (injectiveMoment H (mergeFirst pivotMatrix2988 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2988 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2988 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2988 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2988 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2988, value1614, value1644, value1707, value1714, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2989 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2989 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound2989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2989 = Sparse.eval value2989 (momentVector H) := by
  have heq : pivotMatrix2989 = (fun u v => node2989 (pivotPermutation2989 u) v) := by apply Matrix.ext; unfold pivotMatrix2989 node2989 pivotPermutation2989; decide +kernel
  have hmoment : injectiveMoment H node2989 = injectiveMoment H pivotMatrix2989 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2989 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2989 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2989 (0 : Fin 5)) =
      Sparse.eval value1552 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2989 (0 : Fin 5) = raw1657 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2989 raw1657; decide +kernel
    rw [heq]
    exact (canonical1657 hH).trans (sound1552 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2989 (1 : Fin 5)) =
      Sparse.eval value1710 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2989 (1 : Fin 5) = raw1989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2989 raw1989; decide +kernel
    rw [heq]
    exact (canonical1989 hH).trans (sound1710 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2989 (2 : Fin 5)) =
      Sparse.eval value1716 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2989 (2 : Fin 5) = raw2019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2989 raw2019; decide +kernel
    rw [heq]
    exact (canonical2019 hH).trans (sound1716 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2989 (3 : Fin 5)) =
      Sparse.eval value2627 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2989 (3 : Fin 5) = raw2026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2989 raw2026; decide +kernel
    rw [heq]
    exact (canonical2026 hH).trans (sound2627 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2989 (4 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2989 (4 : Fin 5) = raw2027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2989 raw2027; decide +kernel
    rw [heq]
    exact (canonical2027 hH).trans (sound1718 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2989 + (injectiveMoment H (mergeFirst pivotMatrix2989 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2989 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2989 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2989 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2989 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2989, value1552, value1710, value1716, value1718, value2627, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2990 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2990 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound2990 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2990 = Sparse.eval value2990 (momentVector H) := by
  have heq : pivotMatrix2990 = (fun u v => node2990 (pivotPermutation2990 u) v) := by apply Matrix.ext; unfold pivotMatrix2990 node2990 pivotPermutation2990; decide +kernel
  have hmoment : injectiveMoment H node2990 = injectiveMoment H pivotMatrix2990 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2990 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2990 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2990 (0 : Fin 5)) =
      Sparse.eval value1563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2990 (0 : Fin 5) = raw1660 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2990 raw1660; decide +kernel
    rw [heq]
    exact (canonical1660 hH).trans (sound1563 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2990 (1 : Fin 5)) =
      Sparse.eval value1668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2990 (1 : Fin 5) = raw1993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2990 raw1993; decide +kernel
    rw [heq]
    exact (canonical1993 hH).trans (sound1668 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2990 (2 : Fin 5)) =
      Sparse.eval value2605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2990 (2 : Fin 5) = raw2030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2990 raw2030; decide +kernel
    rw [heq]
    exact (canonical2030 hH).trans (sound2605 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2990 (3 : Fin 5)) =
      Sparse.eval value1669 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2990 (3 : Fin 5) = raw2034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2990 raw2034; decide +kernel
    rw [heq]
    exact (canonical2034 hH).trans (sound1669 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2990 (4 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2990 (4 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2990 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2990 + (injectiveMoment H (mergeFirst pivotMatrix2990 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2990 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2990 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2990 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2990 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2990, value1563, value1668, value1669, value1720, value2605, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2991 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2991 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound2991 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2991 = Sparse.eval value2991 (momentVector H) := by
  have heq : pivotMatrix2991 = (fun u v => node2991 (pivotPermutation2991 u) v) := by apply Matrix.ext; unfold pivotMatrix2991 node2991 pivotPermutation2991; decide +kernel
  have hmoment : injectiveMoment H node2991 = injectiveMoment H pivotMatrix2991 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2991 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2991 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2991 (0 : Fin 5)) =
      Sparse.eval value1617 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2991 (0 : Fin 5) = raw1663 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2991 raw1663; decide +kernel
    rw [heq]
    exact (canonical1663 hH).trans (sound1617 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2991 (1 : Fin 5)) =
      Sparse.eval value1713 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2991 (1 : Fin 5) = raw1996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2991 raw1996; decide +kernel
    rw [heq]
    exact (canonical1996 hH).trans (sound1713 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2991 (2 : Fin 5)) =
      Sparse.eval value1720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2991 (2 : Fin 5) = raw2035 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2991 raw2035; decide +kernel
    rw [heq]
    exact (canonical2035 hH).trans (sound1720 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2991 (3 : Fin 5)) =
      Sparse.eval value1722 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2991 (3 : Fin 5) = raw2039 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2991 raw2039; decide +kernel
    rw [heq]
    exact (canonical2039 hH).trans (sound1722 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2991 (4 : Fin 5)) =
      Sparse.eval value1723 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2991 (4 : Fin 5) = raw2040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2991 raw2040; decide +kernel
    rw [heq]
    exact (canonical2040 hH).trans (sound1723 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2991 + (injectiveMoment H (mergeFirst pivotMatrix2991 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2991 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2991 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2991 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2991 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2991, value1617, value1713, value1720, value1722, value1723, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2992 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2992 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem sound2992 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2992 = Sparse.eval value2992 (momentVector H) := by
  have heq : pivotMatrix2992 = (fun u v => node2992 (pivotPermutation2992 u) v) := by apply Matrix.ext; unfold pivotMatrix2992 node2992 pivotPermutation2992; decide +kernel
  have hmoment : injectiveMoment H node2992 = injectiveMoment H pivotMatrix2992 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2992 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2992 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2992 (0 : Fin 5)) =
      Sparse.eval value1585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2992 (0 : Fin 5) = raw1678 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2992 raw1678; decide +kernel
    rw [heq]
    exact (canonical1678 hH).trans (sound1585 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2992 (1 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2992 (1 : Fin 5) = raw2027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2992 raw2027; decide +kernel
    rw [heq]
    exact (canonical2027 hH).trans (sound1718 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2992 (2 : Fin 5)) =
      Sparse.eval value1718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2992 (2 : Fin 5) = raw2057 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2992 raw2057; decide +kernel
    rw [heq]
    exact (canonical2057 hH).trans (sound1718 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2992 (3 : Fin 5)) =
      Sparse.eval value2640 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2992 (3 : Fin 5) = raw2059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2992 raw2059; decide +kernel
    rw [heq]
    exact (canonical2059 hH).trans (sound2640 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2992 (4 : Fin 5)) =
      Sparse.eval value1724 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2992 (4 : Fin 5) = raw2060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2992 raw2060; decide +kernel
    rw [heq]
    exact (canonical2060 hH).trans (sound1724 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2992 + (injectiveMoment H (mergeFirst pivotMatrix2992 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2992 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2992 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2992 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2992 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2992, value1585, value1718, value1724, value2640, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2993 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2993 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem sound2993 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2993 = Sparse.eval value2993 (momentVector H) := by
  have heq : pivotMatrix2993 = (fun u v => node2993 (pivotPermutation2993 u) v) := by apply Matrix.ext; unfold pivotMatrix2993 node2993 pivotPermutation2993; decide +kernel
  have hmoment : injectiveMoment H node2993 = injectiveMoment H pivotMatrix2993 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2993 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2993 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2993 (0 : Fin 5)) =
      Sparse.eval value1780 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2993 (0 : Fin 5) = raw2314 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2993 raw2314; decide +kernel
    rw [heq]
    exact (canonical2314 hH).trans (sound1780 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2993 (1 : Fin 5)) =
      Sparse.eval value1692 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2993 (1 : Fin 5) = raw1945 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2993 raw1945; decide +kernel
    rw [heq]
    exact (canonical1945 hH).trans (sound1692 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2993 (2 : Fin 5)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2993 (2 : Fin 5) = raw1895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2993 raw1895; decide +kernel
    rw [heq]
    exact (canonical1895 hH).trans (sound1680 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2993 (3 : Fin 5)) =
      Sparse.eval value1676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2993 (3 : Fin 5) = raw1889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2993 raw1889; decide +kernel
    rw [heq]
    exact (canonical1889 hH).trans (sound1676 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2993 (4 : Fin 5)) =
      Sparse.eval value1675 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2993 (4 : Fin 5) = raw1888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2993 raw1888; decide +kernel
    rw [heq]
    exact (canonical1888 hH).trans (sound1675 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2993 + (injectiveMoment H (mergeFirst pivotMatrix2993 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2993 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2993 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2993 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2993 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2993, value1675, value1676, value1680, value1692, value1780, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2994 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2994 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem sound2994 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2994 = Sparse.eval value2994 (momentVector H) := by
  have heq : pivotMatrix2994 = (fun u v => node2994 (pivotPermutation2994 u) v) := by apply Matrix.ext; unfold pivotMatrix2994 node2994 pivotPermutation2994; decide +kernel
  have hmoment : injectiveMoment H node2994 = injectiveMoment H pivotMatrix2994 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2994 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2994 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2994 (0 : Fin 5)) =
      Sparse.eval value1781 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2994 (0 : Fin 5) = raw2315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2994 raw2315; decide +kernel
    rw [heq]
    exact (canonical2315 hH).trans (sound1781 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2994 (1 : Fin 5)) =
      Sparse.eval value1693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2994 (1 : Fin 5) = raw1946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2994 raw1946; decide +kernel
    rw [heq]
    exact (canonical1946 hH).trans (sound1693 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2994 (2 : Fin 5)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2994 (2 : Fin 5) = raw1896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2994 raw1896; decide +kernel
    rw [heq]
    exact (canonical1896 hH).trans (sound2742 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2994 (3 : Fin 5)) =
      Sparse.eval value1677 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2994 (3 : Fin 5) = raw1890 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2994 raw1890; decide +kernel
    rw [heq]
    exact (canonical1890 hH).trans (sound1677 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2994 (4 : Fin 5)) =
      Sparse.eval value1676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2994 (4 : Fin 5) = raw1889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2994 raw1889; decide +kernel
    rw [heq]
    exact (canonical1889 hH).trans (sound1676 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2994 + (injectiveMoment H (mergeFirst pivotMatrix2994 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2994 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2994 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2994 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2994 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2994, value1676, value1677, value1693, value1781, value2742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2995 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2995 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound2995 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2995 = Sparse.eval value2995 (momentVector H) := by
  have heq : pivotMatrix2995 = (fun u v => node2995 (pivotPermutation2995 u) v) := by apply Matrix.ext; unfold pivotMatrix2995 node2995 pivotPermutation2995; decide +kernel
  have hmoment : injectiveMoment H node2995 = injectiveMoment H pivotMatrix2995 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2995 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2995 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2995 (0 : Fin 5)) =
      Sparse.eval value1784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2995 (0 : Fin 5) = raw2318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2995 raw2318; decide +kernel
    rw [heq]
    exact (canonical2318 hH).trans (sound1784 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2995 (1 : Fin 5)) =
      Sparse.eval value1694 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2995 (1 : Fin 5) = raw1947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2995 raw1947; decide +kernel
    rw [heq]
    exact (canonical1947 hH).trans (sound1694 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2995 (2 : Fin 5)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2995 (2 : Fin 5) = raw1899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2995 raw1899; decide +kernel
    rw [heq]
    exact (canonical1899 hH).trans (sound2748 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2995 (3 : Fin 5)) =
      Sparse.eval value1679 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2995 (3 : Fin 5) = raw1892 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2995 raw1892; decide +kernel
    rw [heq]
    exact (canonical1892 hH).trans (sound1679 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2995 (4 : Fin 5)) =
      Sparse.eval value1678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2995 (4 : Fin 5) = raw1891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2995 raw1891; decide +kernel
    rw [heq]
    exact (canonical1891 hH).trans (sound1678 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2995 + (injectiveMoment H (mergeFirst pivotMatrix2995 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2995 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2995 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2995 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2995 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2995, value1678, value1679, value1694, value1784, value2748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2996 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2996 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem sound2996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2996 = Sparse.eval value2996 (momentVector H) := by
  have heq : pivotMatrix2996 = (fun u v => node2996 (pivotPermutation2996 u) v) := by apply Matrix.ext; unfold pivotMatrix2996 node2996 pivotPermutation2996; decide +kernel
  have hmoment : injectiveMoment H node2996 = injectiveMoment H pivotMatrix2996 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2996 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2996 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2996 (0 : Fin 5)) =
      Sparse.eval value1785 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2996 (0 : Fin 5) = raw2321 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2996 raw2321; decide +kernel
    rw [heq]
    exact (canonical2321 hH).trans (sound1785 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2996 (1 : Fin 5)) =
      Sparse.eval value1695 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2996 (1 : Fin 5) = raw1952 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2996 raw1952; decide +kernel
    rw [heq]
    exact (canonical1952 hH).trans (sound1695 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2996 (2 : Fin 5)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2996 (2 : Fin 5) = raw1904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2996 raw1904; decide +kernel
    rw [heq]
    exact (canonical1904 hH).trans (sound2742 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2996 (3 : Fin 5)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2996 (3 : Fin 5) = raw1896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2996 raw1896; decide +kernel
    rw [heq]
    exact (canonical1896 hH).trans (sound2742 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2996 (4 : Fin 5)) =
      Sparse.eval value1680 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2996 (4 : Fin 5) = raw1895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2996 raw1895; decide +kernel
    rw [heq]
    exact (canonical1895 hH).trans (sound1680 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2996 + (injectiveMoment H (mergeFirst pivotMatrix2996 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2996 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2996 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2996 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2996 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2996, value1680, value1695, value1785, value2742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2997 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2997 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem sound2997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2997 = Sparse.eval value2997 (momentVector H) := by
  have heq : pivotMatrix2997 = (fun u v => node2997 (pivotPermutation2997 u) v) := by apply Matrix.ext; unfold pivotMatrix2997 node2997 pivotPermutation2997; decide +kernel
  have hmoment : injectiveMoment H node2997 = injectiveMoment H pivotMatrix2997 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2997 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2997 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2997 (0 : Fin 5)) =
      Sparse.eval value1786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2997 (0 : Fin 5) = raw2322 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2997 raw2322; decide +kernel
    rw [heq]
    exact (canonical2322 hH).trans (sound1786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2997 (1 : Fin 5)) =
      Sparse.eval value1696 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2997 (1 : Fin 5) = raw1953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2997 raw1953; decide +kernel
    rw [heq]
    exact (canonical1953 hH).trans (sound1696 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2997 (2 : Fin 5)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2997 (2 : Fin 5) = raw1905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2997 raw1905; decide +kernel
    rw [heq]
    exact (canonical1905 hH).trans (sound2676 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2997 (3 : Fin 5)) =
      Sparse.eval value1681 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2997 (3 : Fin 5) = raw1897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2997 raw1897; decide +kernel
    rw [heq]
    exact (canonical1897 hH).trans (sound1681 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2997 (4 : Fin 5)) =
      Sparse.eval value2742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2997 (4 : Fin 5) = raw1896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2997 raw1896; decide +kernel
    rw [heq]
    exact (canonical1896 hH).trans (sound2742 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2997 + (injectiveMoment H (mergeFirst pivotMatrix2997 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2997 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2997 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2997 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2997 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2997, value1681, value1696, value1786, value2676, value2742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2998 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2998 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound2998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2998 = Sparse.eval value2998 (momentVector H) := by
  have heq : pivotMatrix2998 = (fun u v => node2998 (pivotPermutation2998 u) v) := by apply Matrix.ext; unfold pivotMatrix2998 node2998 pivotPermutation2998; decide +kernel
  have hmoment : injectiveMoment H node2998 = injectiveMoment H pivotMatrix2998 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2998 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2998 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2998 (0 : Fin 5)) =
      Sparse.eval value1789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2998 (0 : Fin 5) = raw2325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2998 raw2325; decide +kernel
    rw [heq]
    exact (canonical2325 hH).trans (sound1789 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2998 (1 : Fin 5)) =
      Sparse.eval value1697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2998 (1 : Fin 5) = raw1954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2998 raw1954; decide +kernel
    rw [heq]
    exact (canonical1954 hH).trans (sound1697 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2998 (2 : Fin 5)) =
      Sparse.eval value2620 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2998 (2 : Fin 5) = raw1907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2998 raw1907; decide +kernel
    rw [heq]
    exact (canonical1907 hH).trans (sound2620 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2998 (3 : Fin 5)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2998 (3 : Fin 5) = raw1899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2998 raw1899; decide +kernel
    rw [heq]
    exact (canonical1899 hH).trans (sound2748 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2998 (4 : Fin 5)) =
      Sparse.eval value1682 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2998 (4 : Fin 5) = raw1898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2998 raw1898; decide +kernel
    rw [heq]
    exact (canonical1898 hH).trans (sound1682 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2998 + (injectiveMoment H (mergeFirst pivotMatrix2998 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2998 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2998 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2998 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2998 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2998, value1682, value1697, value1789, value2620, value2748, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2999 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2999 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound2999 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2999 = Sparse.eval value2999 (momentVector H) := by
  have heq : pivotMatrix2999 = (fun u v => node2999 (pivotPermutation2999 u) v) := by apply Matrix.ext; unfold pivotMatrix2999 node2999 pivotPermutation2999; decide +kernel
  have hmoment : injectiveMoment H node2999 = injectiveMoment H pivotMatrix2999 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2999 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2999 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2999 (0 : Fin 5)) =
      Sparse.eval value1790 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2999 (0 : Fin 5) = raw2326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2999 raw2326; decide +kernel
    rw [heq]
    exact (canonical2326 hH).trans (sound1790 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2999 (1 : Fin 5)) =
      Sparse.eval value1698 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2999 (1 : Fin 5) = raw1955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2999 raw1955; decide +kernel
    rw [heq]
    exact (canonical1955 hH).trans (sound1698 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2999 (2 : Fin 5)) =
      Sparse.eval value2767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2999 (2 : Fin 5) = raw1908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2999 raw1908; decide +kernel
    rw [heq]
    exact (canonical1908 hH).trans (sound2767 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2999 (3 : Fin 5)) =
      Sparse.eval value1683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2999 (3 : Fin 5) = raw1900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2999 raw1900; decide +kernel
    rw [heq]
    exact (canonical1900 hH).trans (sound1683 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2999 (4 : Fin 5)) =
      Sparse.eval value2748 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2999 (4 : Fin 5) = raw1899 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2999 raw1899; decide +kernel
    rw [heq]
    exact (canonical1899 hH).trans (sound2748 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2999 + (injectiveMoment H (mergeFirst pivotMatrix2999 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2999 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2999 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2999 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2999 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2999, value1683, value1698, value1790, value2748, value2767, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3000 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3000 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem sound3000 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3000 = Sparse.eval value3000 (momentVector H) := by
  have heq : pivotMatrix3000 = (fun u v => node3000 (pivotPermutation3000 u) v) := by apply Matrix.ext; unfold pivotMatrix3000 node3000 pivotPermutation3000; decide +kernel
  have hmoment : injectiveMoment H node3000 = injectiveMoment H pivotMatrix3000 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3000 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3000 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3000 (0 : Fin 5)) =
      Sparse.eval value1791 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3000 (0 : Fin 5) = raw2330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3000 raw2330; decide +kernel
    rw [heq]
    exact (canonical2330 hH).trans (sound1791 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3000 (1 : Fin 5)) =
      Sparse.eval value1699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3000 (1 : Fin 5) = raw1959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3000 raw1959; decide +kernel
    rw [heq]
    exact (canonical1959 hH).trans (sound1699 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3000 (2 : Fin 5)) =
      Sparse.eval value1684 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3000 (2 : Fin 5) = raw1913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3000 raw1913; decide +kernel
    rw [heq]
    exact (canonical1913 hH).trans (sound1684 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3000 (3 : Fin 5)) =
      Sparse.eval value1684 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3000 (3 : Fin 5) = raw1906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3000 raw1906; decide +kernel
    rw [heq]
    exact (canonical1906 hH).trans (sound1684 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3000 (4 : Fin 5)) =
      Sparse.eval value2676 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3000 (4 : Fin 5) = raw1905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3000 raw1905; decide +kernel
    rw [heq]
    exact (canonical1905 hH).trans (sound2676 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3000 + (injectiveMoment H (mergeFirst pivotMatrix3000 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3000 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3000 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3000 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3000 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3000, value1684, value1699, value1791, value2676, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3001 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3001 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound3001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3001 = Sparse.eval value3001 (momentVector H) := by
  have heq : pivotMatrix3001 = (fun u v => node3001 (pivotPermutation3001 u) v) := by apply Matrix.ext; unfold pivotMatrix3001 node3001 pivotPermutation3001; decide +kernel
  have hmoment : injectiveMoment H node3001 = injectiveMoment H pivotMatrix3001 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3001 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3001 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3001 (0 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3001 (0 : Fin 5) = raw2332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3001 raw2332; decide +kernel
    rw [heq]
    exact (canonical2332 hH).trans (sound1793 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3001 (1 : Fin 5)) =
      Sparse.eval value1701 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3001 (1 : Fin 5) = raw1961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3001 raw1961; decide +kernel
    rw [heq]
    exact (canonical1961 hH).trans (sound1701 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3001 (2 : Fin 5)) =
      Sparse.eval value1686 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3001 (2 : Fin 5) = raw1914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3001 raw1914; decide +kernel
    rw [heq]
    exact (canonical1914 hH).trans (sound1686 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3001 (3 : Fin 5)) =
      Sparse.eval value1685 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3001 (3 : Fin 5) = raw1909 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3001 raw1909; decide +kernel
    rw [heq]
    exact (canonical1909 hH).trans (sound1685 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3001 (4 : Fin 5)) =
      Sparse.eval value2767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3001 (4 : Fin 5) = raw1908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3001 raw1908; decide +kernel
    rw [heq]
    exact (canonical1908 hH).trans (sound2767 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3001 + (injectiveMoment H (mergeFirst pivotMatrix3001 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3001 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3001 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3001 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3001 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3001, value1685, value1686, value1701, value1793, value2767, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3002 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3002 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound3002 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3002 = Sparse.eval value3002 (momentVector H) := by
  have heq : pivotMatrix3002 = (fun u v => node3002 (pivotPermutation3002 u) v) := by apply Matrix.ext; unfold pivotMatrix3002 node3002 pivotPermutation3002; decide +kernel
  have hmoment : injectiveMoment H node3002 = injectiveMoment H pivotMatrix3002 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3002 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3002 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3002 (0 : Fin 5)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3002 (0 : Fin 5) = raw2343 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3002 raw2343; decide +kernel
    rw [heq]
    exact (canonical2343 hH).trans (sound1800 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3002 (1 : Fin 5)) =
      Sparse.eval value1702 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3002 (1 : Fin 5) = raw1966 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3002 raw1966; decide +kernel
    rw [heq]
    exact (canonical1966 hH).trans (sound1702 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3002 (2 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3002 (2 : Fin 5) = raw1921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3002 raw1921; decide +kernel
    rw [heq]
    exact (canonical1921 hH).trans (sound2750 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3002 (3 : Fin 5)) =
      Sparse.eval value1688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3002 (3 : Fin 5) = raw1918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3002 raw1918; decide +kernel
    rw [heq]
    exact (canonical1918 hH).trans (sound1688 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3002 (4 : Fin 5)) =
      Sparse.eval value1687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3002 (4 : Fin 5) = raw1917 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3002 raw1917; decide +kernel
    rw [heq]
    exact (canonical1917 hH).trans (sound1687 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3002 + (injectiveMoment H (mergeFirst pivotMatrix3002 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3002 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3002 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3002 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3002 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3002, value1687, value1688, value1702, value1800, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3003 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3003 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound3003 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3003 = Sparse.eval value3003 (momentVector H) := by
  have heq : pivotMatrix3003 = (fun u v => node3003 (pivotPermutation3003 u) v) := by apply Matrix.ext; unfold pivotMatrix3003 node3003 pivotPermutation3003; decide +kernel
  have hmoment : injectiveMoment H node3003 = injectiveMoment H pivotMatrix3003 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3003 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3003 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3003 (0 : Fin 5)) =
      Sparse.eval value1801 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3003 (0 : Fin 5) = raw2347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3003 raw2347; decide +kernel
    rw [heq]
    exact (canonical2347 hH).trans (sound1801 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3003 (1 : Fin 5)) =
      Sparse.eval value1703 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3003 (1 : Fin 5) = raw1968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3003 raw1968; decide +kernel
    rw [heq]
    exact (canonical1968 hH).trans (sound1703 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3003 (2 : Fin 5)) =
      Sparse.eval value2619 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3003 (2 : Fin 5) = raw1925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3003 raw1925; decide +kernel
    rw [heq]
    exact (canonical1925 hH).trans (sound2619 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3003 (3 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3003 (3 : Fin 5) = raw1921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3003 raw1921; decide +kernel
    rw [heq]
    exact (canonical1921 hH).trans (sound2750 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3003 (4 : Fin 5)) =
      Sparse.eval value1689 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3003 (4 : Fin 5) = raw1920 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3003 raw1920; decide +kernel
    rw [heq]
    exact (canonical1920 hH).trans (sound1689 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3003 + (injectiveMoment H (mergeFirst pivotMatrix3003 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3003 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3003 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3003 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3003 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3003, value1689, value1703, value1801, value2619, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3004 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3004 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem sound3004 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3004 = Sparse.eval value3004 (momentVector H) := by
  have heq : pivotMatrix3004 = (fun u v => node3004 (pivotPermutation3004 u) v) := by apply Matrix.ext; unfold pivotMatrix3004 node3004 pivotPermutation3004; decide +kernel
  have hmoment : injectiveMoment H node3004 = injectiveMoment H pivotMatrix3004 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3004 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3004 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3004 (0 : Fin 5)) =
      Sparse.eval value1793 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3004 (0 : Fin 5) = raw2348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3004 raw2348; decide +kernel
    rw [heq]
    exact (canonical2348 hH).trans (sound1793 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3004 (1 : Fin 5)) =
      Sparse.eval value1704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3004 (1 : Fin 5) = raw1969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3004 raw1969; decide +kernel
    rw [heq]
    exact (canonical1969 hH).trans (sound1704 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3004 (2 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3004 (2 : Fin 5) = raw1926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3004 raw1926; decide +kernel
    rw [heq]
    exact (canonical1926 hH).trans (sound2740 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3004 (3 : Fin 5)) =
      Sparse.eval value1690 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3004 (3 : Fin 5) = raw1922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3004 raw1922; decide +kernel
    rw [heq]
    exact (canonical1922 hH).trans (sound1690 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3004 (4 : Fin 5)) =
      Sparse.eval value2750 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3004 (4 : Fin 5) = raw1921 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3004 raw1921; decide +kernel
    rw [heq]
    exact (canonical1921 hH).trans (sound2750 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3004 + (injectiveMoment H (mergeFirst pivotMatrix3004 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3004 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3004 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3004 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3004 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3004, value1690, value1704, value1793, value2740, value2750, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3005 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3005 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem sound3005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3005 = Sparse.eval value3005 (momentVector H) := by
  have heq : pivotMatrix3005 = (fun u v => node3005 (pivotPermutation3005 u) v) := by apply Matrix.ext; unfold pivotMatrix3005 node3005 pivotPermutation3005; decide +kernel
  have hmoment : injectiveMoment H node3005 = injectiveMoment H pivotMatrix3005 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3005 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3005 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3005 (0 : Fin 5)) =
      Sparse.eval value1803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3005 (0 : Fin 5) = raw2351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3005 raw2351; decide +kernel
    rw [heq]
    exact (canonical2351 hH).trans (sound1803 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3005 (1 : Fin 5)) =
      Sparse.eval value1705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3005 (1 : Fin 5) = raw1971 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3005 raw1971; decide +kernel
    rw [heq]
    exact (canonical1971 hH).trans (sound1705 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3005 (2 : Fin 5)) =
      Sparse.eval value1624 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3005 (2 : Fin 5) = raw1930 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3005 raw1930; decide +kernel
    rw [heq]
    exact (canonical1930 hH).trans (sound1624 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3005 (3 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3005 (3 : Fin 5) = raw1926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3005 raw1926; decide +kernel
    rw [heq]
    exact (canonical1926 hH).trans (sound2740 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3005 (4 : Fin 5)) =
      Sparse.eval value2619 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3005 (4 : Fin 5) = raw1925 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3005 raw1925; decide +kernel
    rw [heq]
    exact (canonical1925 hH).trans (sound2619 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3005 + (injectiveMoment H (mergeFirst pivotMatrix3005 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3005 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3005 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3005 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3005 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3005, value1624, value1705, value1803, value2619, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3006 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3006 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem sound3006 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3006 = Sparse.eval value3006 (momentVector H) := by
  have heq : pivotMatrix3006 = (fun u v => node3006 (pivotPermutation3006 u) v) := by apply Matrix.ext; unfold pivotMatrix3006 node3006 pivotPermutation3006; decide +kernel
  have hmoment : injectiveMoment H node3006 = injectiveMoment H pivotMatrix3006 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3006 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3006 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3006 (0 : Fin 5)) =
      Sparse.eval value1804 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3006 (0 : Fin 5) = raw2352 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3006 raw2352; decide +kernel
    rw [heq]
    exact (canonical2352 hH).trans (sound1804 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3006 (1 : Fin 5)) =
      Sparse.eval value1706 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3006 (1 : Fin 5) = raw1972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3006 raw1972; decide +kernel
    rw [heq]
    exact (canonical1972 hH).trans (sound1706 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3006 (2 : Fin 5)) =
      Sparse.eval value1626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3006 (2 : Fin 5) = raw1931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3006 raw1931; decide +kernel
    rw [heq]
    exact (canonical1931 hH).trans (sound1626 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3006 (3 : Fin 5)) =
      Sparse.eval value1691 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3006 (3 : Fin 5) = raw1927 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3006 raw1927; decide +kernel
    rw [heq]
    exact (canonical1927 hH).trans (sound1691 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3006 (4 : Fin 5)) =
      Sparse.eval value2740 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3006 (4 : Fin 5) = raw1926 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3006 raw1926; decide +kernel
    rw [heq]
    exact (canonical1926 hH).trans (sound2740 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3006 + (injectiveMoment H (mergeFirst pivotMatrix3006 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3006 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3006 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3006 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3006 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3006, value1626, value1691, value1706, value1804, value2740, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation3007 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix3007 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound3007 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3007 = Sparse.eval value3007 (momentVector H) := by
  have heq : pivotMatrix3007 = (fun u v => node3007 (pivotPermutation3007 u) v) := by apply Matrix.ext; unfold pivotMatrix3007 node3007 pivotPermutation3007; decide +kernel
  have hmoment : injectiveMoment H node3007 = injectiveMoment H pivotMatrix3007 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3007 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3007 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3007 (0 : Fin 5)) =
      Sparse.eval value1817 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3007 (0 : Fin 5) = raw2392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3007 raw2392; decide +kernel
    rw [heq]
    exact (canonical2392 hH).trans (sound1817 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3007 (1 : Fin 5)) =
      Sparse.eval value1644 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3007 (1 : Fin 5) = raw2017 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3007 raw2017; decide +kernel
    rw [heq]
    exact (canonical2017 hH).trans (sound1644 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3007 (2 : Fin 5)) =
      Sparse.eval value1628 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3007 (2 : Fin 5) = raw1987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3007 raw1987; decide +kernel
    rw [heq]
    exact (canonical1987 hH).trans (sound1628 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3007 (3 : Fin 5)) =
      Sparse.eval value1708 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3007 (3 : Fin 5) = raw1985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3007 raw1985; decide +kernel
    rw [heq]
    exact (canonical1985 hH).trans (sound1708 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3007 (4 : Fin 5)) =
      Sparse.eval value1707 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3007 (4 : Fin 5) = raw1984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3007 raw1984; decide +kernel
    rw [heq]
    exact (canonical1984 hH).trans (sound1707 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3007 + (injectiveMoment H (mergeFirst pivotMatrix3007 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3007 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3007 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3007 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3007 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3007, value1628, value1644, value1707, value1708, value1817, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
