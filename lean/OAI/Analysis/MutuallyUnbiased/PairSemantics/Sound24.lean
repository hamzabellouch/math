import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical54
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical63
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical64
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical194

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1536 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem sound1536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1536 = Sparse.eval value1536 (momentVector H) := by
  have heq : pivotMatrix1536 = (fun u v => node1536 (pivotPermutation1536 u) v) := by apply Matrix.ext; unfold pivotMatrix1536 node1536 pivotPermutation1536; decide +kernel
  have hmoment : injectiveMoment H node1536 = injectiveMoment H pivotMatrix1536 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1536 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1536 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1536 (0 : Fin 5)) =
      Sparse.eval value384 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1536 (0 : Fin 5) = raw931 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1536 raw931; decide +kernel
    rw [heq]
    exact (canonical931 hH).trans (sound384 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1536 (1 : Fin 5)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1536 (1 : Fin 5) = raw1379 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1536 raw1379; decide +kernel
    rw [heq]
    exact (canonical1379 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1536 (2 : Fin 5)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1536 (2 : Fin 5) = raw1393 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1536 raw1393; decide +kernel
    rw [heq]
    exact (canonical1393 hH).trans (sound145 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1536 (3 : Fin 5)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1536 (3 : Fin 5) = raw1397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1536 raw1397; decide +kernel
    rw [heq]
    exact (canonical1397 hH).trans (sound145 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1536 (4 : Fin 5)) =
      Sparse.eval value437 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1536 (4 : Fin 5) = raw1398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1536 raw1398; decide +kernel
    rw [heq]
    exact (canonical1398 hH).trans (sound437 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1536 + (injectiveMoment H (mergeFirst pivotMatrix1536 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1536 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1536 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1536 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1536 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1536, value145, value384, value437, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1537 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem sound1537 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1537 = Sparse.eval value1537 (momentVector H) := by
  have heq : pivotMatrix1537 = (fun u v => node1537 (pivotPermutation1537 u) v) := by apply Matrix.ext; unfold pivotMatrix1537 node1537 pivotPermutation1537; decide +kernel
  have hmoment : injectiveMoment H node1537 = injectiveMoment H pivotMatrix1537 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1537 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1537 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1537 (0 : Fin 5)) =
      Sparse.eval value386 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1537 (0 : Fin 5) = raw933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1537 raw933; decide +kernel
    rw [heq]
    exact (canonical933 hH).trans (sound386 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1537 (1 : Fin 5)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1537 (1 : Fin 5) = raw1380 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1537 raw1380; decide +kernel
    rw [heq]
    exact (canonical1380 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1537 (2 : Fin 5)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1537 (2 : Fin 5) = raw1394 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1537 raw1394; decide +kernel
    rw [heq]
    exact (canonical1394 hH).trans (sound149 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1537 (3 : Fin 5)) =
      Sparse.eval value439 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1537 (3 : Fin 5) = raw1400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1537 raw1400; decide +kernel
    rw [heq]
    exact (canonical1400 hH).trans (sound439 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1537 (4 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1537 (4 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1537 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1537 + (injectiveMoment H (mergeFirst pivotMatrix1537 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1537 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1537 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1537 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1537 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1537, value149, value386, value439, value440, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1538 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem sound1538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1538 = Sparse.eval value1538 (momentVector H) := by
  have heq : pivotMatrix1538 = (fun u v => node1538 (pivotPermutation1538 u) v) := by apply Matrix.ext; unfold pivotMatrix1538 node1538 pivotPermutation1538; decide +kernel
  have hmoment : injectiveMoment H node1538 = injectiveMoment H pivotMatrix1538 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1538 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1538 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1538 (0 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1538 (0 : Fin 5) = raw934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1538 raw934; decide +kernel
    rw [heq]
    exact (canonical934 hH).trans (sound387 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1538 (1 : Fin 5)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1538 (1 : Fin 5) = raw1381 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1538 raw1381; decide +kernel
    rw [heq]
    exact (canonical1381 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1538 (2 : Fin 5)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1538 (2 : Fin 5) = raw1395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1538 raw1395; decide +kernel
    rw [heq]
    exact (canonical1395 hH).trans (sound150 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1538 (3 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1538 (3 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1538 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1538 (4 : Fin 5)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1538 (4 : Fin 5) = raw1402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1538 raw1402; decide +kernel
    rw [heq]
    exact (canonical1402 hH).trans (sound441 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1538 + (injectiveMoment H (mergeFirst pivotMatrix1538 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1538 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1538 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1538 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1538 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1538, value150, value387, value440, value441, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1539 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem sound1539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1539 = Sparse.eval value1539 (momentVector H) := by
  have heq : pivotMatrix1539 = (fun u v => node1539 (pivotPermutation1539 u) v) := by apply Matrix.ext; unfold pivotMatrix1539 node1539 pivotPermutation1539; decide +kernel
  have hmoment : injectiveMoment H node1539 = injectiveMoment H pivotMatrix1539 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1539 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1539 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1539 (0 : Fin 5)) =
      Sparse.eval value389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1539 (0 : Fin 5) = raw939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1539 raw939; decide +kernel
    rw [heq]
    exact (canonical939 hH).trans (sound389 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1539 (1 : Fin 5)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1539 (1 : Fin 5) = raw1383 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1539 raw1383; decide +kernel
    rw [heq]
    exact (canonical1383 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1539 (2 : Fin 5)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1539 (2 : Fin 5) = raw1402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1539 raw1402; decide +kernel
    rw [heq]
    exact (canonical1402 hH).trans (sound441 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1539 (3 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1539 (3 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1539 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1539 (4 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1539 (4 : Fin 5) = raw1408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1539 raw1408; decide +kernel
    rw [heq]
    exact (canonical1408 hH).trans (sound443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1539 + (injectiveMoment H (mergeFirst pivotMatrix1539 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1539 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1539 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1539 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1539 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1539, value145, value389, value441, value443, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1540 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem sound1540 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1540 = Sparse.eval value1540 (momentVector H) := by
  have heq : pivotMatrix1540 = (fun u v => node1540 (pivotPermutation1540 u) v) := by apply Matrix.ext; unfold pivotMatrix1540 node1540 pivotPermutation1540; decide +kernel
  have hmoment : injectiveMoment H node1540 = injectiveMoment H pivotMatrix1540 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1540 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1540 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1540 (0 : Fin 5)) =
      Sparse.eval value390 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1540 (0 : Fin 5) = raw941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1540 raw941; decide +kernel
    rw [heq]
    exact (canonical941 hH).trans (sound390 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1540 (1 : Fin 5)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1540 (1 : Fin 5) = raw1385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1540 raw1385; decide +kernel
    rw [heq]
    exact (canonical1385 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1540 (2 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1540 (2 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1540 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1540 (3 : Fin 5)) =
      Sparse.eval value444 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1540 (3 : Fin 5) = raw1410 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1540 raw1410; decide +kernel
    rw [heq]
    exact (canonical1410 hH).trans (sound444 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1540 (4 : Fin 5)) =
      Sparse.eval value445 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1540 (4 : Fin 5) = raw1411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1540 raw1411; decide +kernel
    rw [heq]
    exact (canonical1411 hH).trans (sound445 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1540 + (injectiveMoment H (mergeFirst pivotMatrix1540 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1540 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1540 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1540 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1540 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1540, value155, value390, value443, value444, value445, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1541 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem sound1541 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1541 = Sparse.eval value1541 (momentVector H) := by
  have heq : pivotMatrix1541 = (fun u v => node1541 (pivotPermutation1541 u) v) := by apply Matrix.ext; unfold pivotMatrix1541 node1541 pivotPermutation1541; decide +kernel
  have hmoment : injectiveMoment H node1541 = injectiveMoment H pivotMatrix1541 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1541 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1541 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1541 (0 : Fin 5)) =
      Sparse.eval value569 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1541 (0 : Fin 5) = raw2799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1541 raw2799; decide +kernel
    rw [heq]
    exact (canonical2799 hH).trans (sound569 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1541 (1 : Fin 5)) =
      Sparse.eval value442 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1541 (1 : Fin 5) = raw1424 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1541 raw1424; decide +kernel
    rw [heq]
    exact (canonical1424 hH).trans (sound442 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1541 (2 : Fin 5)) =
      Sparse.eval value442 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1541 (2 : Fin 5) = raw1406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1541 raw1406; decide +kernel
    rw [heq]
    exact (canonical1406 hH).trans (sound442 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1541 (3 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1541 (3 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1541 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1541 (4 : Fin 5)) =
      Sparse.eval value439 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1541 (4 : Fin 5) = raw1400 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1541 raw1400; decide +kernel
    rw [heq]
    exact (canonical1400 hH).trans (sound439 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1541 + (injectiveMoment H (mergeFirst pivotMatrix1541 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1541 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1541 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1541 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1541 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1541, value439, value440, value442, value569, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1542 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1542 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem sound1542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1542 = Sparse.eval value1542 (momentVector H) := by
  have heq : pivotMatrix1542 = (fun u v => node1542 (pivotPermutation1542 u) v) := by apply Matrix.ext; unfold pivotMatrix1542 node1542 pivotPermutation1542; decide +kernel
  have hmoment : injectiveMoment H node1542 = injectiveMoment H pivotMatrix1542 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1542 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1542 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1542 (0 : Fin 5)) =
      Sparse.eval value570 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1542 (0 : Fin 5) = raw2800 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1542 raw2800; decide +kernel
    rw [heq]
    exact (canonical2800 hH).trans (sound570 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1542 (1 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1542 (1 : Fin 5) = raw1425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1542 raw1425; decide +kernel
    rw [heq]
    exact (canonical1425 hH).trans (sound443 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1542 (2 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1542 (2 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1542 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1542 (3 : Fin 5)) =
      Sparse.eval value441 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1542 (3 : Fin 5) = raw1402 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1542 raw1402; decide +kernel
    rw [heq]
    exact (canonical1402 hH).trans (sound441 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1542 (4 : Fin 5)) =
      Sparse.eval value440 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1542 (4 : Fin 5) = raw1401 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1542 raw1401; decide +kernel
    rw [heq]
    exact (canonical1401 hH).trans (sound440 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1542 + (injectiveMoment H (mergeFirst pivotMatrix1542 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1542 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1542 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1542 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1542 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1542, value440, value441, value443, value570, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1543 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem sound1543 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1543 = Sparse.eval value1543 (momentVector H) := by
  have heq : pivotMatrix1543 = (fun u v => node1543 (pivotPermutation1543 u) v) := by apply Matrix.ext; unfold pivotMatrix1543 node1543 pivotPermutation1543; decide +kernel
  have hmoment : injectiveMoment H node1543 = injectiveMoment H pivotMatrix1543 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1543 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1543 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1543 (0 : Fin 5)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1543 (0 : Fin 5) = raw2809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1543 raw2809; decide +kernel
    rw [heq]
    exact (canonical2809 hH).trans (sound573 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1543 (1 : Fin 5)) =
      Sparse.eval value446 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1543 (1 : Fin 5) = raw1427 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1543 raw1427; decide +kernel
    rw [heq]
    exact (canonical1427 hH).trans (sound446 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1543 (2 : Fin 5)) =
      Sparse.eval value445 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1543 (2 : Fin 5) = raw1411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1543 raw1411; decide +kernel
    rw [heq]
    exact (canonical1411 hH).trans (sound445 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1543 (3 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1543 (3 : Fin 5) = raw1408 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1543 raw1408; decide +kernel
    rw [heq]
    exact (canonical1408 hH).trans (sound443 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1543 (4 : Fin 5)) =
      Sparse.eval value443 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1543 (4 : Fin 5) = raw1407 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1543 raw1407; decide +kernel
    rw [heq]
    exact (canonical1407 hH).trans (sound443 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1543 + (injectiveMoment H (mergeFirst pivotMatrix1543 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1543 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1543 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1543 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1543 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1543, value443, value445, value446, value573, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1544 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1544 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

theorem sound1544 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1544 = Sparse.eval value1544 (momentVector H) := by
  have heq : pivotMatrix1544 = (fun u v => node1544 (pivotPermutation1544 u) v) := by apply Matrix.ext; unfold pivotMatrix1544 node1544 pivotPermutation1544; decide +kernel
  have hmoment : injectiveMoment H node1544 = injectiveMoment H pivotMatrix1544 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1544 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1544 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1544 (0 : Fin 4)) =
      Sparse.eval value1038 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1544 (0 : Fin 4) = raw1000 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1544 raw1000; decide +kernel
    rw [heq]
    exact (canonical1000 hH).trans (sound1038 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1544 (1 : Fin 4)) =
      Sparse.eval value764 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1544 (1 : Fin 4) = raw1521 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1544 raw1521; decide +kernel
    rw [heq]
    exact (canonical1521 hH).trans (sound764 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1544 (2 : Fin 4)) =
      Sparse.eval value1177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1544 (2 : Fin 4) = raw1650 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1544 raw1650; decide +kernel
    rw [heq]
    exact (canonical1650 hH).trans (sound1177 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1544 (3 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1544 (3 : Fin 4) = raw1659 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1544 raw1659; decide +kernel
    rw [heq]
    exact (canonical1659 hH).trans (sound1113 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1544 + (injectiveMoment H (mergeFirst pivotMatrix1544 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1544 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1544 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1544 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1544, value1038, value1113, value1177, value764, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1545 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1545 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem sound1545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1545 = Sparse.eval value1545 (momentVector H) := by
  have heq : pivotMatrix1545 = (fun u v => node1545 (pivotPermutation1545 u) v) := by apply Matrix.ext; unfold pivotMatrix1545 node1545 pivotPermutation1545; decide +kernel
  have hmoment : injectiveMoment H node1545 = injectiveMoment H pivotMatrix1545 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1545 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1545 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1545 (0 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1545 (0 : Fin 4) = raw1014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1545 raw1014; decide +kernel
    rw [heq]
    exact (canonical1014 hH).trans (sound886 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1545 (1 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1545 (1 : Fin 4) = raw1528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1545 raw1528; decide +kernel
    rw [heq]
    exact (canonical1528 hH).trans (sound246 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1545 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1545 (2 : Fin 4) = raw1689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1545 raw1689; decide +kernel
    rw [heq]
    exact (canonical1689 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1545 (3 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1545 (3 : Fin 4) = raw1694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1545 raw1694; decide +kernel
    rw [heq]
    exact (canonical1694 hH).trans (sound1171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1545 + (injectiveMoment H (mergeFirst pivotMatrix1545 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1545 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1545 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1545 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1545, value1171, value246, value886, value894, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1546 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1546 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1546 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1546 = Sparse.eval value1546 (momentVector H) := by
  have heq : pivotMatrix1546 = (fun u v => node1546 (pivotPermutation1546 u) v) := by apply Matrix.ext; unfold pivotMatrix1546 node1546 pivotPermutation1546; decide +kernel
  have hmoment : injectiveMoment H node1546 = injectiveMoment H pivotMatrix1546 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1546 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1546 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1546 (0 : Fin 4)) =
      Sparse.eval value886 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1546 (0 : Fin 4) = raw1023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1546 raw1023; decide +kernel
    rw [heq]
    exact (canonical1023 hH).trans (sound886 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1546 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1546 (1 : Fin 4) = raw1642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1546 raw1642; decide +kernel
    rw [heq]
    exact (canonical1642 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1546 (2 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1546 (2 : Fin 4) = raw1705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1546 raw1705; decide +kernel
    rw [heq]
    exact (canonical1705 hH).trans (sound1080 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1546 (3 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1546 (3 : Fin 4) = raw1708 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1546 raw1708; decide +kernel
    rw [heq]
    exact (canonical1708 hH).trans (sound1042 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1546 + (injectiveMoment H (mergeFirst pivotMatrix1546 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1546 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1546 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1546 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1546, value1042, value1080, value769, value886, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1547 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1547 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem sound1547 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1547 = Sparse.eval value1547 (momentVector H) := by
  have heq : pivotMatrix1547 = (fun u v => node1547 (pivotPermutation1547 u) v) := by apply Matrix.ext; unfold pivotMatrix1547 node1547 pivotPermutation1547; decide +kernel
  have hmoment : injectiveMoment H node1547 = injectiveMoment H pivotMatrix1547 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1547 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1547 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1547 (0 : Fin 4)) =
      Sparse.eval value1233 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1547 (0 : Fin 4) = raw1027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1547 raw1027; decide +kernel
    rw [heq]
    exact (canonical1027 hH).trans (sound1233 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1547 (1 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1547 (1 : Fin 4) = raw1691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1547 raw1691; decide +kernel
    rw [heq]
    exact (canonical1691 hH).trans (sound1171 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1547 (2 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1547 (2 : Fin 4) = raw1720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1547 raw1720; decide +kernel
    rw [heq]
    exact (canonical1720 hH).trans (sound460 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1547 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1547 (3 : Fin 4) = raw1724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1547 raw1724; decide +kernel
    rw [heq]
    exact (canonical1724 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1547 + (injectiveMoment H (mergeFirst pivotMatrix1547 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1547 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1547 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1547 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1547, value1171, value1233, value1234, value460, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1548 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1548 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem sound1548 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1548 = Sparse.eval value1548 (momentVector H) := by
  have heq : pivotMatrix1548 = (fun u v => node1548 (pivotPermutation1548 u) v) := by apply Matrix.ext; unfold pivotMatrix1548 node1548 pivotPermutation1548; decide +kernel
  have hmoment : injectiveMoment H node1548 = injectiveMoment H pivotMatrix1548 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1548 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1548 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1548 (0 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1548 (0 : Fin 4) = raw1065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1548 raw1065; decide +kernel
    rw [heq]
    exact (canonical1065 hH).trans (sound914 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1548 (1 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1548 (1 : Fin 4) = raw1493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1548 raw1493; decide +kernel
    rw [heq]
    exact (canonical1493 hH).trans (sound917 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1548 (2 : Fin 4)) =
      Sparse.eval value907 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1548 (2 : Fin 4) = raw1558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1548 raw1558; decide +kernel
    rw [heq]
    exact (canonical1558 hH).trans (sound907 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1548 (3 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1548 (3 : Fin 4) = raw1581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1548 raw1581; decide +kernel
    rw [heq]
    exact (canonical1581 hH).trans (sound915 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1548 + (injectiveMoment H (mergeFirst pivotMatrix1548 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1548 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1548 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1548 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1548, value907, value914, value915, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1549 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1549 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem sound1549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1549 = Sparse.eval value1549 (momentVector H) := by
  have heq : pivotMatrix1549 = (fun u v => node1549 (pivotPermutation1549 u) v) := by apply Matrix.ext; unfold pivotMatrix1549 node1549 pivotPermutation1549; decide +kernel
  have hmoment : injectiveMoment H node1549 = injectiveMoment H pivotMatrix1549 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1549 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1549 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1549 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1549 (0 : Fin 4) = raw1072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1549 raw1072; decide +kernel
    rw [heq]
    exact (canonical1072 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1549 (1 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1549 (1 : Fin 4) = raw1499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1549 raw1499; decide +kernel
    rw [heq]
    exact (canonical1499 hH).trans (sound449 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1549 (2 : Fin 4)) =
      Sparse.eval value915 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1549 (2 : Fin 4) = raw1581 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1549 raw1581; decide +kernel
    rw [heq]
    exact (canonical1581 hH).trans (sound915 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1549 (3 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1549 (3 : Fin 4) = raw1599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1549 raw1599; decide +kernel
    rw [heq]
    exact (canonical1599 hH).trans (sound917 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1549 + (injectiveMoment H (mergeFirst pivotMatrix1549 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1549 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1549 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1549 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1549, value449, value775, value915, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1550 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1550 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem sound1550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1550 = Sparse.eval value1550 (momentVector H) := by
  have heq : pivotMatrix1550 = (fun u v => node1550 (pivotPermutation1550 u) v) := by apply Matrix.ext; unfold pivotMatrix1550 node1550 pivotPermutation1550; decide +kernel
  have hmoment : injectiveMoment H node1550 = injectiveMoment H pivotMatrix1550 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1550 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1550 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1550 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1550 (0 : Fin 4) = raw1074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1550 raw1074; decide +kernel
    rw [heq]
    exact (canonical1074 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1550 (1 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1550 (1 : Fin 4) = raw1501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1550 raw1501; decide +kernel
    rw [heq]
    exact (canonical1501 hH).trans (sound450 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1550 (2 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1550 (2 : Fin 4) = raw1587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1550 raw1587; decide +kernel
    rw [heq]
    exact (canonical1587 hH).trans (sound769 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1550 (3 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1550 (3 : Fin 4) = raw1604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1550 raw1604; decide +kernel
    rw [heq]
    exact (canonical1604 hH).trans (sound774 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1550 + (injectiveMoment H (mergeFirst pivotMatrix1550 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1550 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1550 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1550 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1550, value450, value769, value774, value775, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1551 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1551 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem sound1551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1551 = Sparse.eval value1551 (momentVector H) := by
  have heq : pivotMatrix1551 = (fun u v => node1551 (pivotPermutation1551 u) v) := by apply Matrix.ext; unfold pivotMatrix1551 node1551 pivotPermutation1551; decide +kernel
  have hmoment : injectiveMoment H node1551 = injectiveMoment H pivotMatrix1551 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1551 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1551 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1551 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1551 (0 : Fin 4) = raw1076 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1551 raw1076; decide +kernel
    rw [heq]
    exact (canonical1076 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1551 (1 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1551 (1 : Fin 4) = raw1503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1551 raw1503; decide +kernel
    rw [heq]
    exact (canonical1503 hH).trans (sound1278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1551 (2 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1551 (2 : Fin 4) = raw1610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1551 raw1610; decide +kernel
    rw [heq]
    exact (canonical1610 hH).trans (sound1171 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1551 (3 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1551 (3 : Fin 4) = raw1613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1551 raw1613; decide +kernel
    rw [heq]
    exact (canonical1613 hH).trans (sound1176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1551 + (injectiveMoment H (mergeFirst pivotMatrix1551 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1551 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1551 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1551 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1551, value1171, value1176, value1178, value1278, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1552 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1552 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem sound1552 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1552 = Sparse.eval value1552 (momentVector H) := by
  have heq : pivotMatrix1552 = (fun u v => node1552 (pivotPermutation1552 u) v) := by apply Matrix.ext; unfold pivotMatrix1552 node1552 pivotPermutation1552; decide +kernel
  have hmoment : injectiveMoment H node1552 = injectiveMoment H pivotMatrix1552 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1552 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1552 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1552 (0 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1552 (0 : Fin 4) = raw1077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1552 raw1077; decide +kernel
    rw [heq]
    exact (canonical1077 hH).trans (sound914 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1552 (1 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1552 (1 : Fin 4) = raw1504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1552 raw1504; decide +kernel
    rw [heq]
    exact (canonical1504 hH).trans (sound896 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1552 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1552 (2 : Fin 4) = raw1611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1552 raw1611; decide +kernel
    rw [heq]
    exact (canonical1611 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1552 (3 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1552 (3 : Fin 4) = raw1614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1552 raw1614; decide +kernel
    rw [heq]
    exact (canonical1614 hH).trans (sound910 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1552 + (injectiveMoment H (mergeFirst pivotMatrix1552 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1552 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1552 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1552 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1552, value894, value896, value910, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1553 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1553 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem sound1553 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1553 = Sparse.eval value1553 (momentVector H) := by
  have heq : pivotMatrix1553 = (fun u v => node1553 (pivotPermutation1553 u) v) := by apply Matrix.ext; unfold pivotMatrix1553 node1553 pivotPermutation1553; decide +kernel
  have hmoment : injectiveMoment H node1553 = injectiveMoment H pivotMatrix1553 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1553 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1553 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1553 (0 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1553 (0 : Fin 4) = raw1079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1553 raw1079; decide +kernel
    rw [heq]
    exact (canonical1079 hH).trans (sound787 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1553 (1 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1553 (1 : Fin 4) = raw1507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1553 raw1507; decide +kernel
    rw [heq]
    exact (canonical1507 hH).trans (sound454 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1553 (2 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1553 (2 : Fin 4) = raw1614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1553 raw1614; decide +kernel
    rw [heq]
    exact (canonical1614 hH).trans (sound910 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1553 (3 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1553 (3 : Fin 4) = raw1616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1553 raw1616; decide +kernel
    rw [heq]
    exact (canonical1616 hH).trans (sound766 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1553 + (injectiveMoment H (mergeFirst pivotMatrix1553 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1553 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1553 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1553 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1553, value454, value766, value787, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1554 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1554 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem sound1554 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1554 = Sparse.eval value1554 (momentVector H) := by
  have heq : pivotMatrix1554 = (fun u v => node1554 (pivotPermutation1554 u) v) := by apply Matrix.ext; unfold pivotMatrix1554 node1554 pivotPermutation1554; decide +kernel
  have hmoment : injectiveMoment H node1554 = injectiveMoment H pivotMatrix1554 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1554 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1554 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1554 (0 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1554 (0 : Fin 4) = raw1124 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1554 raw1124; decide +kernel
    rw [heq]
    exact (canonical1124 hH).trans (sound1037 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1554 (1 : Fin 4)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1554 (1 : Fin 4) = raw1525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1554 raw1525; decide +kernel
    rw [heq]
    exact (canonical1525 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1554 (2 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1554 (2 : Fin 4) = raw1651 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1554 raw1651; decide +kernel
    rw [heq]
    exact (canonical1651 hH).trans (sound775 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1554 (3 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1554 (3 : Fin 4) = raw1659 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1554 raw1659; decide +kernel
    rw [heq]
    exact (canonical1659 hH).trans (sound1113 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1554 + (injectiveMoment H (mergeFirst pivotMatrix1554 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1554 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1554 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1554 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1554, value1037, value1113, value145, value775, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1555 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1555 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem sound1555 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1555 = Sparse.eval value1555 (momentVector H) := by
  have heq : pivotMatrix1555 = (fun u v => node1555 (pivotPermutation1555 u) v) := by apply Matrix.ext; unfold pivotMatrix1555 node1555 pivotPermutation1555; decide +kernel
  have hmoment : injectiveMoment H node1555 = injectiveMoment H pivotMatrix1555 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1555 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1555 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1555 (0 : Fin 4)) =
      Sparse.eval value1070 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (0 : Fin 4) = raw1128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1128; decide +kernel
    rw [heq]
    exact (canonical1128 hH).trans (sound1070 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1555 (1 : Fin 4)) =
      Sparse.eval value286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (1 : Fin 4) = raw1526 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1526; decide +kernel
    rw [heq]
    exact (canonical1526 hH).trans (sound286 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1555 (2 : Fin 4)) =
      Sparse.eval value1272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (2 : Fin 4) = raw1664 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1664; decide +kernel
    rw [heq]
    exact (canonical1664 hH).trans (sound1272 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1555 (3 : Fin 4)) =
      Sparse.eval value981 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1555 (3 : Fin 4) = raw1667 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1555 raw1667; decide +kernel
    rw [heq]
    exact (canonical1667 hH).trans (sound981 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1555 + (injectiveMoment H (mergeFirst pivotMatrix1555 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1555 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1555 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1555 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1555, value1070, value1272, value286, value981, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1556 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem sound1556 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1556 = Sparse.eval value1556 (momentVector H) := by
  have heq : pivotMatrix1556 = (fun u v => node1556 (pivotPermutation1556 u) v) := by apply Matrix.ext; unfold pivotMatrix1556 node1556 pivotPermutation1556; decide +kernel
  have hmoment : injectiveMoment H node1556 = injectiveMoment H pivotMatrix1556 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1556 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1556 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1556 (0 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1556 (0 : Fin 4) = raw1130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1556 raw1130; decide +kernel
    rw [heq]
    exact (canonical1130 hH).trans (sound998 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1556 (1 : Fin 4)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1556 (1 : Fin 4) = raw1527 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1556 raw1527; decide +kernel
    rw [heq]
    exact (canonical1527 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1556 (2 : Fin 4)) =
      Sparse.eval value1100 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1556 (2 : Fin 4) = raw1666 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1556 raw1666; decide +kernel
    rw [heq]
    exact (canonical1666 hH).trans (sound1100 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1556 (3 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1556 (3 : Fin 4) = raw1669 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1556 raw1669; decide +kernel
    rw [heq]
    exact (canonical1669 hH).trans (sound787 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1556 + (injectiveMoment H (mergeFirst pivotMatrix1556 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1556 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1556 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1556 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1556, value1100, value150, value787, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1557 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1557 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1557 = Sparse.eval value1557 (momentVector H) := by
  have heq : pivotMatrix1557 = (fun u v => node1557 (pivotPermutation1557 u) v) := by apply Matrix.ext; unfold pivotMatrix1557 node1557 pivotPermutation1557; decide +kernel
  have hmoment : injectiveMoment H node1557 = injectiveMoment H pivotMatrix1557 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1557 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1557 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1557 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1557 (0 : Fin 4) = raw1139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1557 raw1139; decide +kernel
    rw [heq]
    exact (canonical1139 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1557 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1557 (1 : Fin 4) = raw1587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1557 raw1587; decide +kernel
    rw [heq]
    exact (canonical1587 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1557 (2 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1557 (2 : Fin 4) = raw1673 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1557 raw1673; decide +kernel
    rw [heq]
    exact (canonical1673 hH).trans (sound774 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1557 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1557 (3 : Fin 4) = raw1683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1557 raw1683; decide +kernel
    rw [heq]
    exact (canonical1683 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1557 + (injectiveMoment H (mergeFirst pivotMatrix1557 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1557 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1557 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1557 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1557, value769, value771, value774, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1558 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound1558 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1558 = Sparse.eval value1558 (momentVector H) := by
  have heq : pivotMatrix1558 = (fun u v => node1558 (pivotPermutation1558 u) v) := by apply Matrix.ext; unfold pivotMatrix1558 node1558 pivotPermutation1558; decide +kernel
  have hmoment : injectiveMoment H node1558 = injectiveMoment H pivotMatrix1558 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1558 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1558 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1558 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1558 (0 : Fin 4) = raw1142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1558 raw1142; decide +kernel
    rw [heq]
    exact (canonical1142 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1558 (1 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1558 (1 : Fin 4) = raw1613 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1558 raw1613; decide +kernel
    rw [heq]
    exact (canonical1613 hH).trans (sound1176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1558 (2 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1558 (2 : Fin 4) = raw1687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1558 raw1687; decide +kernel
    rw [heq]
    exact (canonical1687 hH).trans (sound1176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1558 (3 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1558 (3 : Fin 4) = raw1691 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1558 raw1691; decide +kernel
    rw [heq]
    exact (canonical1691 hH).trans (sound1171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1558 + (injectiveMoment H (mergeFirst pivotMatrix1558 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1558 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1558 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1558 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1558, value1168, value1171, value1176, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1559 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1559 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem sound1559 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1559 = Sparse.eval value1559 (momentVector H) := by
  have heq : pivotMatrix1559 = (fun u v => node1559 (pivotPermutation1559 u) v) := by apply Matrix.ext; unfold pivotMatrix1559 node1559 pivotPermutation1559; decide +kernel
  have hmoment : injectiveMoment H node1559 = injectiveMoment H pivotMatrix1559 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1559 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1559 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1559 (0 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1559 (0 : Fin 4) = raw1143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1559 raw1143; decide +kernel
    rw [heq]
    exact (canonical1143 hH).trans (sound786 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1559 (1 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1559 (1 : Fin 4) = raw1615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1559 raw1615; decide +kernel
    rw [heq]
    exact (canonical1615 hH).trans (sound766 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1559 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1559 (2 : Fin 4) = raw1689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1559 raw1689; decide +kernel
    rw [heq]
    exact (canonical1689 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1559 (3 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1559 (3 : Fin 4) = raw1693 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1559 raw1693; decide +kernel
    rw [heq]
    exact (canonical1693 hH).trans (sound910 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1559 + (injectiveMoment H (mergeFirst pivotMatrix1559 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1559 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1559 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1559 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1559, value766, value786, value894, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1560 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1560 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound1560 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1560 = Sparse.eval value1560 (momentVector H) := by
  have heq : pivotMatrix1560 = (fun u v => node1560 (pivotPermutation1560 u) v) := by apply Matrix.ext; unfold pivotMatrix1560 node1560 pivotPermutation1560; decide +kernel
  have hmoment : injectiveMoment H node1560 = injectiveMoment H pivotMatrix1560 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1560 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1560 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1560 (0 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1560 (0 : Fin 4) = raw1151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1560 raw1151; decide +kernel
    rw [heq]
    exact (canonical1151 hH).trans (sound998 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1560 (1 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1560 (1 : Fin 4) = raw1641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1560 raw1641; decide +kernel
    rw [heq]
    exact (canonical1641 hH).trans (sound771 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1560 (2 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1560 (2 : Fin 4) = raw1699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1560 raw1699; decide +kernel
    rw [heq]
    exact (canonical1699 hH).trans (sound786 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1560 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1560 (3 : Fin 4) = raw1702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1560 raw1702; decide +kernel
    rw [heq]
    exact (canonical1702 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1560 + (injectiveMoment H (mergeFirst pivotMatrix1560 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1560 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1560 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1560 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1560, value771, value786, value998, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1561 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1561 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem sound1561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1561 = Sparse.eval value1561 (momentVector H) := by
  have heq : pivotMatrix1561 = (fun u v => node1561 (pivotPermutation1561 u) v) := by apply Matrix.ext; unfold pivotMatrix1561 node1561 pivotPermutation1561; decide +kernel
  have hmoment : injectiveMoment H node1561 = injectiveMoment H pivotMatrix1561 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1561 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1561 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1561 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1561 (0 : Fin 4) = raw1163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1561 raw1163; decide +kernel
    rw [heq]
    exact (canonical1163 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1561 (1 : Fin 4)) =
      Sparse.eval value910 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1561 (1 : Fin 4) = raw1692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1561 raw1692; decide +kernel
    rw [heq]
    exact (canonical1692 hH).trans (sound910 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1561 (2 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1561 (2 : Fin 4) = raw1716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1561 raw1716; decide +kernel
    rw [heq]
    exact (canonical1716 hH).trans (sound454 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1561 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1561 (3 : Fin 4) = raw1719 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1561 raw1719; decide +kernel
    rw [heq]
    exact (canonical1719 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1561 + (injectiveMoment H (mergeFirst pivotMatrix1561 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1561 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1561 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1561 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1561, value454, value771, value896, value910, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1562 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1562 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem sound1562 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1562 = Sparse.eval value1562 (momentVector H) := by
  have heq : pivotMatrix1562 = (fun u v => node1562 (pivotPermutation1562 u) v) := by apply Matrix.ext; unfold pivotMatrix1562 node1562 pivotPermutation1562; decide +kernel
  have hmoment : injectiveMoment H node1562 = injectiveMoment H pivotMatrix1562 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1562 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1562 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1562 (0 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1562 (0 : Fin 4) = raw1164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1562 raw1164; decide +kernel
    rw [heq]
    exact (canonical1164 hH).trans (sound1037 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1562 (1 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1562 (1 : Fin 4) = raw1702 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1562 raw1702; decide +kernel
    rw [heq]
    exact (canonical1702 hH).trans (sound786 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1562 (2 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1562 (2 : Fin 4) = raw1721 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1562 raw1721; decide +kernel
    rw [heq]
    exact (canonical1721 hH).trans (sound771 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1562 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1562 (3 : Fin 4) = raw1724 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1562 raw1724; decide +kernel
    rw [heq]
    exact (canonical1724 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1562 + (injectiveMoment H (mergeFirst pivotMatrix1562 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1562 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1562 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1562 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1562, value1037, value1234, value771, value786, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1563 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1563 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem sound1563 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1563 = Sparse.eval value1563 (momentVector H) := by
  have heq : pivotMatrix1563 = (fun u v => node1563 (pivotPermutation1563 u) v) := by apply Matrix.ext; unfold pivotMatrix1563 node1563 pivotPermutation1563; decide +kernel
  have hmoment : injectiveMoment H node1563 = injectiveMoment H pivotMatrix1563 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1563 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1563 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1563 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1563 (0 : Fin 4) = raw1165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1563 raw1165; decide +kernel
    rw [heq]
    exact (canonical1165 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1563 (1 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1563 (1 : Fin 4) = raw1707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1563 raw1707; decide +kernel
    rw [heq]
    exact (canonical1707 hH).trans (sound1042 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1563 (2 : Fin 4)) =
      Sparse.eval value1042 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1563 (2 : Fin 4) = raw1726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1563 raw1726; decide +kernel
    rw [heq]
    exact (canonical1726 hH).trans (sound1042 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1563 (3 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1563 (3 : Fin 4) = raw1728 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1563 raw1728; decide +kernel
    rw [heq]
    exact (canonical1728 hH).trans (sound1080 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1563 + (injectiveMoment H (mergeFirst pivotMatrix1563 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1563 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1563 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1563 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1563, value1031, value1042, value1080, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1564 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1564 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem sound1564 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1564 = Sparse.eval value1564 (momentVector H) := by
  have heq : pivotMatrix1564 = (fun u v => node1564 (pivotPermutation1564 u) v) := by apply Matrix.ext; unfold pivotMatrix1564 node1564 pivotPermutation1564; decide +kernel
  have hmoment : injectiveMoment H node1564 = injectiveMoment H pivotMatrix1564 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1564 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1564 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1564 (0 : Fin 4)) =
      Sparse.eval value1347 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1564 (0 : Fin 4) = raw1777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1564 raw1777; decide +kernel
    rw [heq]
    exact (canonical1777 hH).trans (sound1347 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1564 (1 : Fin 4)) =
      Sparse.eval value1090 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1564 (1 : Fin 4) = raw1512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1564 raw1512; decide +kernel
    rw [heq]
    exact (canonical1512 hH).trans (sound1090 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1564 (2 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1564 (2 : Fin 4) = raw1493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1564 raw1493; decide +kernel
    rw [heq]
    exact (canonical1493 hH).trans (sound917 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1564 (3 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1564 (3 : Fin 4) = raw1486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1564 raw1486; decide +kernel
    rw [heq]
    exact (canonical1486 hH).trans (sound1348 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1564 + (injectiveMoment H (mergeFirst pivotMatrix1564 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1564 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1564 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1564 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1564, value1090, value1347, value1348, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1565 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1565 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem sound1565 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1565 = Sparse.eval value1565 (momentVector H) := by
  have heq : pivotMatrix1565 = (fun u v => node1565 (pivotPermutation1565 u) v) := by apply Matrix.ext; unfold pivotMatrix1565 node1565 pivotPermutation1565; decide +kernel
  have hmoment : injectiveMoment H node1565 = injectiveMoment H pivotMatrix1565 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1565 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1565 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1565 (0 : Fin 4)) =
      Sparse.eval value975 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1565 (0 : Fin 4) = raw1784 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1565 raw1784; decide +kernel
    rw [heq]
    exact (canonical1784 hH).trans (sound975 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1565 (1 : Fin 4)) =
      Sparse.eval value777 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1565 (1 : Fin 4) = raw1513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1565 raw1513; decide +kernel
    rw [heq]
    exact (canonical1513 hH).trans (sound777 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1565 (2 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1565 (2 : Fin 4) = raw1494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1565 raw1494; decide +kernel
    rw [heq]
    exact (canonical1494 hH).trans (sound447 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1565 (3 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1565 (3 : Fin 4) = raw1493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1565 raw1493; decide +kernel
    rw [heq]
    exact (canonical1493 hH).trans (sound917 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1565 + (injectiveMoment H (mergeFirst pivotMatrix1565 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1565 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1565 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1565 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1565, value447, value777, value917, value975, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1566 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1566 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem sound1566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1566 = Sparse.eval value1566 (momentVector H) := by
  have heq : pivotMatrix1566 = (fun u v => node1566 (pivotPermutation1566 u) v) := by apply Matrix.ext; unfold pivotMatrix1566 node1566 pivotPermutation1566; decide +kernel
  have hmoment : injectiveMoment H node1566 = injectiveMoment H pivotMatrix1566 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1566 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1566 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1566 (0 : Fin 4)) =
      Sparse.eval value472 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1566 (0 : Fin 4) = raw1786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1566 raw1786; decide +kernel
    rw [heq]
    exact (canonical1786 hH).trans (sound472 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1566 (1 : Fin 4)) =
      Sparse.eval value455 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1566 (1 : Fin 4) = raw1514 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1566 raw1514; decide +kernel
    rw [heq]
    exact (canonical1514 hH).trans (sound455 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1566 (2 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1566 (2 : Fin 4) = raw1499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1566 raw1499; decide +kernel
    rw [heq]
    exact (canonical1499 hH).trans (sound449 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1566 (3 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1566 (3 : Fin 4) = raw1496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1566 raw1496; decide +kernel
    rw [heq]
    exact (canonical1496 hH).trans (sound448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1566 + (injectiveMoment H (mergeFirst pivotMatrix1566 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1566 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1566 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1566 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1566, value448, value449, value455, value472, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1567 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1567 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem sound1567 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1567 = Sparse.eval value1567 (momentVector H) := by
  have heq : pivotMatrix1567 = (fun u v => node1567 (pivotPermutation1567 u) v) := by apply Matrix.ext; unfold pivotMatrix1567 node1567 pivotPermutation1567; decide +kernel
  have hmoment : injectiveMoment H node1567 = injectiveMoment H pivotMatrix1567 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1567 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1567 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1567 (0 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1567 (0 : Fin 4) = raw1788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1567 raw1788; decide +kernel
    rw [heq]
    exact (canonical1788 hH).trans (sound473 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1567 (1 : Fin 4)) =
      Sparse.eval value456 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1567 (1 : Fin 4) = raw1515 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1567 raw1515; decide +kernel
    rw [heq]
    exact (canonical1515 hH).trans (sound456 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1567 (2 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1567 (2 : Fin 4) = raw1501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1567 raw1501; decide +kernel
    rw [heq]
    exact (canonical1501 hH).trans (sound450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1567 (3 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1567 (3 : Fin 4) = raw1499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1567 raw1499; decide +kernel
    rw [heq]
    exact (canonical1499 hH).trans (sound449 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1567 + (injectiveMoment H (mergeFirst pivotMatrix1567 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1567 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1567 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1567 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1567, value449, value450, value456, value473, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1568 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1568 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem sound1568 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1568 = Sparse.eval value1568 (momentVector H) := by
  have heq : pivotMatrix1568 = (fun u v => node1568 (pivotPermutation1568 u) v) := by apply Matrix.ext; unfold pivotMatrix1568 node1568 pivotPermutation1568; decide +kernel
  have hmoment : injectiveMoment H node1568 = injectiveMoment H pivotMatrix1568 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1568 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1568 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1568 (0 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1568 (0 : Fin 4) = raw1791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1568 raw1791; decide +kernel
    rw [heq]
    exact (canonical1791 hH).trans (sound474 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1568 (1 : Fin 4)) =
      Sparse.eval value457 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1568 (1 : Fin 4) = raw1516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1568 raw1516; decide +kernel
    rw [heq]
    exact (canonical1516 hH).trans (sound457 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1568 (2 : Fin 4)) =
      Sparse.eval value451 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1568 (2 : Fin 4) = raw1502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1568 raw1502; decide +kernel
    rw [heq]
    exact (canonical1502 hH).trans (sound451 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1568 (3 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1568 (3 : Fin 4) = raw1501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1568 raw1501; decide +kernel
    rw [heq]
    exact (canonical1501 hH).trans (sound450 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1568 + (injectiveMoment H (mergeFirst pivotMatrix1568 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1568 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1568 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1568 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1568, value450, value451, value457, value474, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1569 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1569 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem sound1569 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1569 = Sparse.eval value1569 (momentVector H) := by
  have heq : pivotMatrix1569 = (fun u v => node1569 (pivotPermutation1569 u) v) := by apply Matrix.ext; unfold pivotMatrix1569 node1569 pivotPermutation1569; decide +kernel
  have hmoment : injectiveMoment H node1569 = injectiveMoment H pivotMatrix1569 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1569 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1569 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1569 (0 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1569 (0 : Fin 4) = raw1793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1569 raw1793; decide +kernel
    rw [heq]
    exact (canonical1793 hH).trans (sound1277 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1569 (1 : Fin 4)) =
      Sparse.eval value988 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1569 (1 : Fin 4) = raw1517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1569 raw1517; decide +kernel
    rw [heq]
    exact (canonical1517 hH).trans (sound988 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1569 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1569 (2 : Fin 4) = raw1504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1569 raw1504; decide +kernel
    rw [heq]
    exact (canonical1504 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1569 (3 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1569 (3 : Fin 4) = raw1503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1569 raw1503; decide +kernel
    rw [heq]
    exact (canonical1503 hH).trans (sound1278 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1569 + (injectiveMoment H (mergeFirst pivotMatrix1569 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1569 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1569 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1569 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1569, value1277, value1278, value896, value988, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1570 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1570 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem sound1570 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1570 = Sparse.eval value1570 (momentVector H) := by
  have heq : pivotMatrix1570 = (fun u v => node1570 (pivotPermutation1570 u) v) := by apply Matrix.ext; unfold pivotMatrix1570 node1570 pivotPermutation1570; decide +kernel
  have hmoment : injectiveMoment H node1570 = injectiveMoment H pivotMatrix1570 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1570 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1570 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1570 (0 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1570 (0 : Fin 4) = raw1794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1570 raw1794; decide +kernel
    rw [heq]
    exact (canonical1794 hH).trans (sound944 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1570 (1 : Fin 4)) =
      Sparse.eval value759 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1570 (1 : Fin 4) = raw1518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1570 raw1518; decide +kernel
    rw [heq]
    exact (canonical1518 hH).trans (sound759 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1570 (2 : Fin 4)) =
      Sparse.eval value452 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1570 (2 : Fin 4) = raw1505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1570 raw1505; decide +kernel
    rw [heq]
    exact (canonical1505 hH).trans (sound452 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1570 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1570 (3 : Fin 4) = raw1504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1570 raw1504; decide +kernel
    rw [heq]
    exact (canonical1504 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1570 + (injectiveMoment H (mergeFirst pivotMatrix1570 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1570 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1570 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1570 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1570, value452, value759, value896, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1571 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1571 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem sound1571 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1571 = Sparse.eval value1571 (momentVector H) := by
  have heq : pivotMatrix1571 = (fun u v => node1571 (pivotPermutation1571 u) v) := by apply Matrix.ext; unfold pivotMatrix1571 node1571 pivotPermutation1571; decide +kernel
  have hmoment : injectiveMoment H node1571 = injectiveMoment H pivotMatrix1571 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1571 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1571 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1571 (0 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1571 (0 : Fin 4) = raw1795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1571 raw1795; decide +kernel
    rw [heq]
    exact (canonical1795 hH).trans (sound476 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1571 (1 : Fin 4)) =
      Sparse.eval value458 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1571 (1 : Fin 4) = raw1519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1571 raw1519; decide +kernel
    rw [heq]
    exact (canonical1519 hH).trans (sound458 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1571 (2 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1571 (2 : Fin 4) = raw1507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1571 raw1507; decide +kernel
    rw [heq]
    exact (canonical1507 hH).trans (sound454 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1571 (3 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1571 (3 : Fin 4) = raw1506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1571 raw1506; decide +kernel
    rw [heq]
    exact (canonical1506 hH).trans (sound453 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1571 + (injectiveMoment H (mergeFirst pivotMatrix1571 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1571 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1571 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1571 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1571, value453, value454, value458, value476, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1572 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1572 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem sound1572 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1572 = Sparse.eval value1572 (momentVector H) := by
  have heq : pivotMatrix1572 = (fun u v => node1572 (pivotPermutation1572 u) v) := by apply Matrix.ext; unfold pivotMatrix1572 node1572 pivotPermutation1572; decide +kernel
  have hmoment : injectiveMoment H node1572 = injectiveMoment H pivotMatrix1572 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1572 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1572 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1572 (0 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1572 (0 : Fin 4) = raw2922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1572 raw2922; decide +kernel
    rw [heq]
    exact (canonical2922 hH).trans (sound1234 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1572 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1572 (1 : Fin 4) = raw1587 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1572 raw1587; decide +kernel
    rw [heq]
    exact (canonical1587 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1572 (2 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1572 (2 : Fin 4) = raw1501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1572 raw1501; decide +kernel
    rw [heq]
    exact (canonical1501 hH).trans (sound450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1572 (3 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1572 (3 : Fin 4) = raw1494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1572 raw1494; decide +kernel
    rw [heq]
    exact (canonical1494 hH).trans (sound447 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1572 + (injectiveMoment H (mergeFirst pivotMatrix1572 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1572 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1572 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1572 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1572, value1234, value447, value450, value769, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1573 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1573 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem sound1573 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1573 = Sparse.eval value1573 (momentVector H) := by
  have heq : pivotMatrix1573 = (fun u v => node1573 (pivotPermutation1573 u) v) := by apply Matrix.ext; unfold pivotMatrix1573 node1573 pivotPermutation1573; decide +kernel
  have hmoment : injectiveMoment H node1573 = injectiveMoment H pivotMatrix1573 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1573 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1573 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1573 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1573 (0 : Fin 4) = raw3074 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1573 raw3074; decide +kernel
    rw [heq]
    exact (canonical3074 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1573 (1 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1573 (1 : Fin 4) = raw1627 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1573 raw1627; decide +kernel
    rw [heq]
    exact (canonical1627 hH).trans (sound774 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1573 (2 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1573 (2 : Fin 4) = raw1501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1573 raw1501; decide +kernel
    rw [heq]
    exact (canonical1501 hH).trans (sound450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1573 (3 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1573 (3 : Fin 4) = raw1493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1573 raw1493; decide +kernel
    rw [heq]
    exact (canonical1493 hH).trans (sound917 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1573 + (injectiveMoment H (mergeFirst pivotMatrix1573 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1573 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1573 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1573 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1573, value450, value774, value917, value946, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1574 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1574 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem sound1574 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1574 = Sparse.eval value1574 (momentVector H) := by
  have heq : pivotMatrix1574 = (fun u v => node1574 (pivotPermutation1574 u) v) := by apply Matrix.ext; unfold pivotMatrix1574 node1574 pivotPermutation1574; decide +kernel
  have hmoment : injectiveMoment H node1574 = injectiveMoment H pivotMatrix1574 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1574 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1574 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1574 (0 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1574 (0 : Fin 4) = raw3075 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1574 raw3075; decide +kernel
    rw [heq]
    exact (canonical3075 hH).trans (sound1235 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1574 (1 : Fin 4)) =
      Sparse.eval value773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1574 (1 : Fin 4) = raw1629 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1574 raw1629; decide +kernel
    rw [heq]
    exact (canonical1629 hH).trans (sound773 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1574 (2 : Fin 4)) =
      Sparse.eval value451 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1574 (2 : Fin 4) = raw1502 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1574 raw1502; decide +kernel
    rw [heq]
    exact (canonical1502 hH).trans (sound451 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1574 (3 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1574 (3 : Fin 4) = raw1494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1574 raw1494; decide +kernel
    rw [heq]
    exact (canonical1494 hH).trans (sound447 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1574 + (injectiveMoment H (mergeFirst pivotMatrix1574 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1574 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1574 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1574 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1574, value1235, value447, value451, value773, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1575 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1575 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem sound1575 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1575 = Sparse.eval value1575 (momentVector H) := by
  have heq : pivotMatrix1575 = (fun u v => node1575 (pivotPermutation1575 u) v) := by apply Matrix.ext; unfold pivotMatrix1575 node1575 pivotPermutation1575; decide +kernel
  have hmoment : injectiveMoment H node1575 = injectiveMoment H pivotMatrix1575 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1575 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1575 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1575 (0 : Fin 4)) =
      Sparse.eval value1003 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1575 (0 : Fin 4) = raw3081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1575 raw3081; decide +kernel
    rw [heq]
    exact (canonical3081 hH).trans (sound1003 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1575 (1 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1575 (1 : Fin 4) = raw1641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1575 raw1641; decide +kernel
    rw [heq]
    exact (canonical1641 hH).trans (sound771 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1575 (2 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1575 (2 : Fin 4) = raw1507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1575 raw1507; decide +kernel
    rw [heq]
    exact (canonical1507 hH).trans (sound454 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1575 (3 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1575 (3 : Fin 4) = raw1503 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1575 raw1503; decide +kernel
    rw [heq]
    exact (canonical1503 hH).trans (sound1278 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1575 + (injectiveMoment H (mergeFirst pivotMatrix1575 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1575 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1575 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1575 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1575, value1003, value1278, value454, value771, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1576 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1576 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem sound1576 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1576 = Sparse.eval value1576 (momentVector H) := by
  have heq : pivotMatrix1576 = (fun u v => node1576 (pivotPermutation1576 u) v) := by apply Matrix.ext; unfold pivotMatrix1576 node1576 pivotPermutation1576; decide +kernel
  have hmoment : injectiveMoment H node1576 = injectiveMoment H pivotMatrix1576 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1576 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1576 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1576 (0 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (0 : Fin 4) = raw3082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw3082; decide +kernel
    rw [heq]
    exact (canonical3082 hH).trans (sound939 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1576 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (1 : Fin 4) = raw1642 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw1642; decide +kernel
    rw [heq]
    exact (canonical1642 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1576 (2 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (2 : Fin 4) = raw1508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw1508; decide +kernel
    rw [heq]
    exact (canonical1508 hH).trans (sound454 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1576 (3 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1576 (3 : Fin 4) = raw1504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1576 raw1504; decide +kernel
    rw [heq]
    exact (canonical1504 hH).trans (sound896 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1576 + (injectiveMoment H (mergeFirst pivotMatrix1576 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1576 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1576 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1576 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1576, value454, value769, value896, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1577 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1577 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem sound1577 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1577 = Sparse.eval value1577 (momentVector H) := by
  have heq : pivotMatrix1577 = (fun u v => node1577 (pivotPermutation1577 u) v) := by apply Matrix.ext; unfold pivotMatrix1577 node1577 pivotPermutation1577; decide +kernel
  have hmoment : injectiveMoment H node1577 = injectiveMoment H pivotMatrix1577 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1577 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1577 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1577 (0 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1577 (0 : Fin 4) = raw3083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1577 raw3083; decide +kernel
    rw [heq]
    exact (canonical3083 hH).trans (sound1007 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1577 (1 : Fin 4)) =
      Sparse.eval value772 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1577 (1 : Fin 4) = raw1643 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1577 raw1643; decide +kernel
    rw [heq]
    exact (canonical1643 hH).trans (sound772 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1577 (2 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1577 (2 : Fin 4) = raw1509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1577 raw1509; decide +kernel
    rw [heq]
    exact (canonical1509 hH).trans (sound453 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1577 (3 : Fin 4)) =
      Sparse.eval value452 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1577 (3 : Fin 4) = raw1505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1577 raw1505; decide +kernel
    rw [heq]
    exact (canonical1505 hH).trans (sound452 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1577 + (injectiveMoment H (mergeFirst pivotMatrix1577 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1577 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1577 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1577 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1577, value1007, value452, value453, value772, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1578 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1578 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem sound1578 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1578 = Sparse.eval value1578 (momentVector H) := by
  have heq : pivotMatrix1578 = (fun u v => node1578 (pivotPermutation1578 u) v) := by apply Matrix.ext; unfold pivotMatrix1578 node1578 pivotPermutation1578; decide +kernel
  have hmoment : injectiveMoment H node1578 = injectiveMoment H pivotMatrix1578 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1578 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1578 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1578 (0 : Fin 4)) =
      Sparse.eval value944 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1578 (0 : Fin 4) = raw6222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1578 raw6222; decide +kernel
    rw [heq]
    exact (canonical6222 hH).trans (sound944 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1578 (1 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1578 (1 : Fin 4) = raw1734 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1578 raw1734; decide +kernel
    rw [heq]
    exact (canonical1734 hH).trans (sound469 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1578 (2 : Fin 4)) =
      Sparse.eval value452 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1578 (2 : Fin 4) = raw1510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1578 raw1510; decide +kernel
    rw [heq]
    exact (canonical1510 hH).trans (sound452 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1578 (3 : Fin 4)) =
      Sparse.eval value448 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1578 (3 : Fin 4) = raw1496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1578 raw1496; decide +kernel
    rw [heq]
    exact (canonical1496 hH).trans (sound448 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1578 + (injectiveMoment H (mergeFirst pivotMatrix1578 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1578 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1578 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1578 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1578, value448, value452, value469, value944, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1579 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1579 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem sound1579 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1579 = Sparse.eval value1579 (momentVector H) := by
  have heq : pivotMatrix1579 = (fun u v => node1579 (pivotPermutation1579 u) v) := by apply Matrix.ext; unfold pivotMatrix1579 node1579 pivotPermutation1579; decide +kernel
  have hmoment : injectiveMoment H node1579 = injectiveMoment H pivotMatrix1579 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1579 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1579 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1579 (0 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1579 (0 : Fin 4) = raw6043 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1579 raw6043; decide +kernel
    rw [heq]
    exact (canonical6043 hH).trans (sound896 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1579 (1 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1579 (1 : Fin 4) = raw1731 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1579 raw1731; decide +kernel
    rw [heq]
    exact (canonical1731 hH).trans (sound454 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1579 (2 : Fin 4)) =
      Sparse.eval value452 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1579 (2 : Fin 4) = raw1510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1579 raw1510; decide +kernel
    rw [heq]
    exact (canonical1510 hH).trans (sound452 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1579 (3 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1579 (3 : Fin 4) = raw1499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1579 raw1499; decide +kernel
    rw [heq]
    exact (canonical1499 hH).trans (sound449 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1579 + (injectiveMoment H (mergeFirst pivotMatrix1579 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1579 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1579 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1579 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1579, value449, value452, value454, value896, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1580 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1580 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem sound1580 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1580 = Sparse.eval value1580 (momentVector H) := by
  have heq : pivotMatrix1580 = (fun u v => node1580 (pivotPermutation1580 u) v) := by apply Matrix.ext; unfold pivotMatrix1580 node1580 pivotPermutation1580; decide +kernel
  have hmoment : injectiveMoment H node1580 = injectiveMoment H pivotMatrix1580 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1580 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1580 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1580 (0 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (0 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1580 (1 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (1 : Fin 4) = raw1735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw1735; decide +kernel
    rw [heq]
    exact (canonical1735 hH).trans (sound896 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1580 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (2 : Fin 4) = raw1511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw1511; decide +kernel
    rw [heq]
    exact (canonical1511 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1580 (3 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (3 : Fin 4) = raw1499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw1499; decide +kernel
    rw [heq]
    exact (canonical1499 hH).trans (sound449 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1580 + (injectiveMoment H (mergeFirst pivotMatrix1580 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1580 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1580 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1580 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1580, value449, value896, value945, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1581 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1581 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem sound1581 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1581 = Sparse.eval value1581 (momentVector H) := by
  have heq : pivotMatrix1581 = (fun u v => node1581 (pivotPermutation1581 u) v) := by apply Matrix.ext; unfold pivotMatrix1581 node1581 pivotPermutation1581; decide +kernel
  have hmoment : injectiveMoment H node1581 = injectiveMoment H pivotMatrix1581 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1581 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1581 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1581 (0 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1581 (0 : Fin 4) = raw6044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1581 raw6044; decide +kernel
    rw [heq]
    exact (canonical6044 hH).trans (sound774 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1581 (1 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1581 (1 : Fin 4) = raw1732 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1581 raw1732; decide +kernel
    rw [heq]
    exact (canonical1732 hH).trans (sound769 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1581 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1581 (2 : Fin 4) = raw1511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1581 raw1511; decide +kernel
    rw [heq]
    exact (canonical1511 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1581 (3 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1581 (3 : Fin 4) = raw1501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1581 raw1501; decide +kernel
    rw [heq]
    exact (canonical1501 hH).trans (sound450 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1581 + (injectiveMoment H (mergeFirst pivotMatrix1581 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1581 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1581 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1581 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1581, value450, value769, value774, value896, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1582 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1582 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem sound1582 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1582 = Sparse.eval value1582 (momentVector H) := by
  have heq : pivotMatrix1582 = (fun u v => node1582 (pivotPermutation1582 u) v) := by apply Matrix.ext; unfold pivotMatrix1582 node1582 pivotPermutation1582; decide +kernel
  have hmoment : injectiveMoment H node1582 = injectiveMoment H pivotMatrix1582 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1582 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1582 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1582 (0 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1582 (0 : Fin 4) = raw1919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1582 raw1919; decide +kernel
    rw [heq]
    exact (canonical1919 hH).trans (sound1223 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1582 (1 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1582 (1 : Fin 4) = raw1632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1582 raw1632; decide +kernel
    rw [heq]
    exact (canonical1632 hH).trans (sound459 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1582 (2 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1582 (2 : Fin 4) = raw1599 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1582 raw1599; decide +kernel
    rw [heq]
    exact (canonical1599 hH).trans (sound917 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1582 (3 : Fin 4)) =
      Sparse.eval value1179 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1582 (3 : Fin 4) = raw1593 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1582 raw1593; decide +kernel
    rw [heq]
    exact (canonical1593 hH).trans (sound1179 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1582 + (injectiveMoment H (mergeFirst pivotMatrix1582 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1582 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1582 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1582 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1582, value1179, value1223, value459, value917, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1583 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1583 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

theorem sound1583 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1583 = Sparse.eval value1583 (momentVector H) := by
  have heq : pivotMatrix1583 = (fun u v => node1583 (pivotPermutation1583 u) v) := by apply Matrix.ext; unfold pivotMatrix1583 node1583 pivotPermutation1583; decide +kernel
  have hmoment : injectiveMoment H node1583 = injectiveMoment H pivotMatrix1583 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1583 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1583 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1583 (0 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1583 (0 : Fin 4) = raw1929 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1583 raw1929; decide +kernel
    rw [heq]
    exact (canonical1929 hH).trans (sound807 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1583 (1 : Fin 4)) =
      Sparse.eval value396 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1583 (1 : Fin 4) = raw1637 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1583 raw1637; decide +kernel
    rw [heq]
    exact (canonical1637 hH).trans (sound396 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1583 (2 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1583 (2 : Fin 4) = raw1608 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1583 raw1608; decide +kernel
    rw [heq]
    exact (canonical1608 hH).trans (sound1173 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1583 (3 : Fin 4)) =
      Sparse.eval value774 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1583 (3 : Fin 4) = raw1604 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1583 raw1604; decide +kernel
    rw [heq]
    exact (canonical1604 hH).trans (sound774 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1583 + (injectiveMoment H (mergeFirst pivotMatrix1583 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1583 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1583 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1583 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1583, value1173, value396, value774, value807, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1584 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1584 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem sound1584 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1584 = Sparse.eval value1584 (momentVector H) := by
  have heq : pivotMatrix1584 = (fun u v => node1584 (pivotPermutation1584 u) v) := by apply Matrix.ext; unfold pivotMatrix1584 node1584 pivotPermutation1584; decide +kernel
  have hmoment : injectiveMoment H node1584 = injectiveMoment H pivotMatrix1584 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1584 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1584 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1584 (0 : Fin 4)) =
      Sparse.eval value1094 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1584 (0 : Fin 4) = raw1933 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1584 raw1933; decide +kernel
    rw [heq]
    exact (canonical1933 hH).trans (sound1094 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1584 (1 : Fin 4)) =
      Sparse.eval value460 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1584 (1 : Fin 4) = raw1638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1584 raw1638; decide +kernel
    rw [heq]
    exact (canonical1638 hH).trans (sound460 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1584 (2 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1584 (2 : Fin 4) = raw1610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1584 raw1610; decide +kernel
    rw [heq]
    exact (canonical1610 hH).trans (sound1171 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1584 (3 : Fin 4)) =
      Sparse.eval value1324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1584 (3 : Fin 4) = raw1609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1584 raw1609; decide +kernel
    rw [heq]
    exact (canonical1609 hH).trans (sound1324 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1584 + (injectiveMoment H (mergeFirst pivotMatrix1584 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1584 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1584 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1584 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1584, value1094, value1171, value1324, value460, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1585 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1585 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem sound1585 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1585 = Sparse.eval value1585 (momentVector H) := by
  have heq : pivotMatrix1585 = (fun u v => node1585 (pivotPermutation1585 u) v) := by apply Matrix.ext; unfold pivotMatrix1585 node1585 pivotPermutation1585; decide +kernel
  have hmoment : injectiveMoment H node1585 = injectiveMoment H pivotMatrix1585 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1585 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1585 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1585 (0 : Fin 4)) =
      Sparse.eval value1207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1585 (0 : Fin 4) = raw1934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1585 raw1934; decide +kernel
    rw [heq]
    exact (canonical1934 hH).trans (sound1207 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1585 (1 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1585 (1 : Fin 4) = raw1639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1585 raw1639; decide +kernel
    rw [heq]
    exact (canonical1639 hH).trans (sound1234 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1585 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1585 (2 : Fin 4) = raw1611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1585 raw1611; decide +kernel
    rw [heq]
    exact (canonical1611 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1585 (3 : Fin 4)) =
      Sparse.eval value1171 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1585 (3 : Fin 4) = raw1610 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1585 raw1610; decide +kernel
    rw [heq]
    exact (canonical1610 hH).trans (sound1171 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1585 + (injectiveMoment H (mergeFirst pivotMatrix1585 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1585 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1585 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1585 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1585, value1171, value1207, value1234, value894, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1586 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1586 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

theorem sound1586 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1586 = Sparse.eval value1586 (momentVector H) := by
  have heq : pivotMatrix1586 = (fun u v => node1586 (pivotPermutation1586 u) v) := by apply Matrix.ext; unfold pivotMatrix1586 node1586 pivotPermutation1586; decide +kernel
  have hmoment : injectiveMoment H node1586 = injectiveMoment H pivotMatrix1586 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1586 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1586 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1586 (0 : Fin 4)) =
      Sparse.eval value943 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1586 (0 : Fin 4) = raw1935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1586 raw1935; decide +kernel
    rw [heq]
    exact (canonical1935 hH).trans (sound943 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1586 (1 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1586 (1 : Fin 4) = raw1640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1586 raw1640; decide +kernel
    rw [heq]
    exact (canonical1640 hH).trans (sound447 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1586 (2 : Fin 4)) =
      Sparse.eval value756 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1586 (2 : Fin 4) = raw1612 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1586 raw1612; decide +kernel
    rw [heq]
    exact (canonical1612 hH).trans (sound756 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1586 (3 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1586 (3 : Fin 4) = raw1611 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1586 raw1611; decide +kernel
    rw [heq]
    exact (canonical1611 hH).trans (sound894 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1586 + (injectiveMoment H (mergeFirst pivotMatrix1586 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1586 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1586 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1586 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1586, value447, value756, value894, value943, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1587 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1587 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem sound1587 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1587 = Sparse.eval value1587 (momentVector H) := by
  have heq : pivotMatrix1587 = (fun u v => node1587 (pivotPermutation1587 u) v) := by apply Matrix.ext; unfold pivotMatrix1587 node1587 pivotPermutation1587; decide +kernel
  have hmoment : injectiveMoment H node1587 = injectiveMoment H pivotMatrix1587 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1587 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1587 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1587 (0 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1587 (0 : Fin 4) = raw1967 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1587 raw1967; decide +kernel
    rw [heq]
    exact (canonical1967 hH).trans (sound474 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1587 (1 : Fin 4)) =
      Sparse.eval value461 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1587 (1 : Fin 4) = raw1648 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1587 raw1648; decide +kernel
    rw [heq]
    exact (canonical1648 hH).trans (sound461 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1587 (2 : Fin 4)) =
      Sparse.eval value450 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1587 (2 : Fin 4) = raw1634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1587 raw1634; decide +kernel
    rw [heq]
    exact (canonical1634 hH).trans (sound450 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1587 (3 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1587 (3 : Fin 4) = raw1632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1587 raw1632; decide +kernel
    rw [heq]
    exact (canonical1632 hH).trans (sound459 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1587 + (injectiveMoment H (mergeFirst pivotMatrix1587 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1587 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1587 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1587 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1587, value450, value459, value461, value474, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1588 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1588 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem sound1588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1588 = Sparse.eval value1588 (momentVector H) := by
  have heq : pivotMatrix1588 = (fun u v => node1588 (pivotPermutation1588 u) v) := by apply Matrix.ext; unfold pivotMatrix1588 node1588 pivotPermutation1588; decide +kernel
  have hmoment : injectiveMoment H node1588 = injectiveMoment H pivotMatrix1588 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1588 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1588 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1588 (0 : Fin 4)) =
      Sparse.eval value1235 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1588 (0 : Fin 4) = raw1976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1588 raw1976; decide +kernel
    rw [heq]
    exact (canonical1976 hH).trans (sound1235 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1588 (1 : Fin 4)) =
      Sparse.eval value1086 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1588 (1 : Fin 4) = raw1649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1588 raw1649; decide +kernel
    rw [heq]
    exact (canonical1649 hH).trans (sound1086 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1588 (2 : Fin 4)) =
      Sparse.eval value447 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1588 (2 : Fin 4) = raw1640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1588 raw1640; decide +kernel
    rw [heq]
    exact (canonical1640 hH).trans (sound447 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1588 (3 : Fin 4)) =
      Sparse.eval value1234 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1588 (3 : Fin 4) = raw1639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1588 raw1639; decide +kernel
    rw [heq]
    exact (canonical1639 hH).trans (sound1234 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1588 + (injectiveMoment H (mergeFirst pivotMatrix1588 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1588 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1588 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1588 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1588, value1086, value1234, value1235, value447, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1589 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1589 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem sound1589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1589 = Sparse.eval value1589 (momentVector H) := by
  have heq : pivotMatrix1589 = (fun u v => node1589 (pivotPermutation1589 u) v) := by apply Matrix.ext; unfold pivotMatrix1589 node1589 pivotPermutation1589; decide +kernel
  have hmoment : injectiveMoment H node1589 = injectiveMoment H pivotMatrix1589 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1589 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1589 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1589 (0 : Fin 4)) =
      Sparse.eval value1028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1589 (0 : Fin 4) = raw2023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1589 raw2023; decide +kernel
    rw [heq]
    exact (canonical2023 hH).trans (sound1028 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1589 (1 : Fin 4)) =
      Sparse.eval value1108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1589 (1 : Fin 4) = raw1675 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1589 raw1675; decide +kernel
    rw [heq]
    exact (canonical1675 hH).trans (sound1108 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1589 (2 : Fin 4)) =
      Sparse.eval value1108 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1589 (2 : Fin 4) = raw1658 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1589 raw1658; decide +kernel
    rw [heq]
    exact (canonical1658 hH).trans (sound1108 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1589 (3 : Fin 4)) =
      Sparse.eval value957 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1589 (3 : Fin 4) = raw1654 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1589 raw1654; decide +kernel
    rw [heq]
    exact (canonical1654 hH).trans (sound957 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1589 + (injectiveMoment H (mergeFirst pivotMatrix1589 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1589 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1589 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1589 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1589, value1028, value1108, value957, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1590 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1590 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem sound1590 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1590 = Sparse.eval value1590 (momentVector H) := by
  have heq : pivotMatrix1590 = (fun u v => node1590 (pivotPermutation1590 u) v) := by apply Matrix.ext; unfold pivotMatrix1590 node1590 pivotPermutation1590; decide +kernel
  have hmoment : injectiveMoment H node1590 = injectiveMoment H pivotMatrix1590 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1590 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1590 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1590 (0 : Fin 4)) =
      Sparse.eval value805 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1590 (0 : Fin 4) = raw2063 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1590 raw2063; decide +kernel
    rw [heq]
    exact (canonical2063 hH).trans (sound805 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1590 (1 : Fin 4)) =
      Sparse.eval value398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1590 (1 : Fin 4) = raw1697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1590 raw1697; decide +kernel
    rw [heq]
    exact (canonical1697 hH).trans (sound398 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1590 (2 : Fin 4)) =
      Sparse.eval value1173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1590 (2 : Fin 4) = raw1685 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1590 raw1685; decide +kernel
    rw [heq]
    exact (canonical1685 hH).trans (sound1173 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1590 (3 : Fin 4)) =
      Sparse.eval value769 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1590 (3 : Fin 4) = raw1683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1590 raw1683; decide +kernel
    rw [heq]
    exact (canonical1683 hH).trans (sound769 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1590 + (injectiveMoment H (mergeFirst pivotMatrix1590 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1590 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1590 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1590 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1590, value1173, value398, value769, value805, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1591 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1591 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound1591 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1591 = Sparse.eval value1591 (momentVector H) := by
  have heq : pivotMatrix1591 = (fun u v => node1591 (pivotPermutation1591 u) v) := by apply Matrix.ext; unfold pivotMatrix1591 node1591 pivotPermutation1591; decide +kernel
  have hmoment : injectiveMoment H node1591 = injectiveMoment H pivotMatrix1591 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1591 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1591 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1591 (0 : Fin 4)) =
      Sparse.eval value933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1591 (0 : Fin 4) = raw2068 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1591 raw2068; decide +kernel
    rw [heq]
    exact (canonical2068 hH).trans (sound933 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1591 (1 : Fin 4)) =
      Sparse.eval value463 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1591 (1 : Fin 4) = raw1698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1591 raw1698; decide +kernel
    rw [heq]
    exact (canonical1698 hH).trans (sound463 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1591 (2 : Fin 4)) =
      Sparse.eval value1176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1591 (2 : Fin 4) = raw1687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1591 raw1687; decide +kernel
    rw [heq]
    exact (canonical1687 hH).trans (sound1176 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1591 (3 : Fin 4)) =
      Sparse.eval value1324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1591 (3 : Fin 4) = raw1686 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1591 raw1686; decide +kernel
    rw [heq]
    exact (canonical1686 hH).trans (sound1324 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1591 + (injectiveMoment H (mergeFirst pivotMatrix1591 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1591 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1591 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1591 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1591, value1176, value1324, value463, value933, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1592 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1592 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem sound1592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1592 = Sparse.eval value1592 (momentVector H) := by
  have heq : pivotMatrix1592 = (fun u v => node1592 (pivotPermutation1592 u) v) := by apply Matrix.ext; unfold pivotMatrix1592 node1592 pivotPermutation1592; decide +kernel
  have hmoment : injectiveMoment H node1592 = injectiveMoment H pivotMatrix1592 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1592 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1592 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1592 (0 : Fin 4)) =
      Sparse.eval value936 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1592 (0 : Fin 4) = raw2069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1592 raw2069; decide +kernel
    rw [heq]
    exact (canonical2069 hH).trans (sound936 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1592 (1 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1592 (1 : Fin 4) = raw1700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1592 raw1700; decide +kernel
    rw [heq]
    exact (canonical1700 hH).trans (sound464 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1592 (2 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1592 (2 : Fin 4) = raw1689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1592 raw1689; decide +kernel
    rw [heq]
    exact (canonical1689 hH).trans (sound894 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1592 (3 : Fin 4)) =
      Sparse.eval value766 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1592 (3 : Fin 4) = raw1688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1592 raw1688; decide +kernel
    rw [heq]
    exact (canonical1688 hH).trans (sound766 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1592 + (injectiveMoment H (mergeFirst pivotMatrix1592 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1592 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1592 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1592 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1592, value464, value766, value894, value936, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1593 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1593 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

theorem sound1593 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1593 = Sparse.eval value1593 (momentVector H) := by
  have heq : pivotMatrix1593 = (fun u v => node1593 (pivotPermutation1593 u) v) := by apply Matrix.ext; unfold pivotMatrix1593 node1593 pivotPermutation1593; decide +kernel
  have hmoment : injectiveMoment H node1593 = injectiveMoment H pivotMatrix1593 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1593 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1593 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1593 (0 : Fin 4)) =
      Sparse.eval value1098 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1593 (0 : Fin 4) = raw2070 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1593 raw2070; decide +kernel
    rw [heq]
    exact (canonical2070 hH).trans (sound1098 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1593 (1 : Fin 4)) =
      Sparse.eval value465 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1593 (1 : Fin 4) = raw1701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1593 raw1701; decide +kernel
    rw [heq]
    exact (canonical1701 hH).trans (sound465 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1593 (2 : Fin 4)) =
      Sparse.eval value1097 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1593 (2 : Fin 4) = raw1690 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1593 raw1690; decide +kernel
    rw [heq]
    exact (canonical1690 hH).trans (sound1097 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1593 (3 : Fin 4)) =
      Sparse.eval value894 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1593 (3 : Fin 4) = raw1689 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1593 raw1689; decide +kernel
    rw [heq]
    exact (canonical1689 hH).trans (sound894 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1593 + (injectiveMoment H (mergeFirst pivotMatrix1593 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1593 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1593 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1593 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1593, value1097, value1098, value465, value894, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1594 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1594 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem sound1594 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1594 = Sparse.eval value1594 (momentVector H) := by
  have heq : pivotMatrix1594 = (fun u v => node1594 (pivotPermutation1594 u) v) := by apply Matrix.ext; unfold pivotMatrix1594 node1594 pivotPermutation1594; decide +kernel
  have hmoment : injectiveMoment H node1594 = injectiveMoment H pivotMatrix1594 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1594 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1594 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1594 (0 : Fin 4)) =
      Sparse.eval value995 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1594 (0 : Fin 4) = raw2080 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1594 raw2080; decide +kernel
    rw [heq]
    exact (canonical2080 hH).trans (sound995 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1594 (1 : Fin 4)) =
      Sparse.eval value466 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1594 (1 : Fin 4) = raw1704 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1594 raw1704; decide +kernel
    rw [heq]
    exact (canonical1704 hH).trans (sound466 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1594 (2 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1594 (2 : Fin 4) = raw1699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1594 raw1699; decide +kernel
    rw [heq]
    exact (canonical1699 hH).trans (sound786 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1594 (3 : Fin 4)) =
      Sparse.eval value463 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1594 (3 : Fin 4) = raw1698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1594 raw1698; decide +kernel
    rw [heq]
    exact (canonical1698 hH).trans (sound463 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1594 + (injectiveMoment H (mergeFirst pivotMatrix1594 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1594 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1594 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1594 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1594, value463, value466, value786, value995, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1595 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1595 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem sound1595 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1595 = Sparse.eval value1595 (momentVector H) := by
  have heq : pivotMatrix1595 = (fun u v => node1595 (pivotPermutation1595 u) v) := by apply Matrix.ext; unfold pivotMatrix1595 node1595 pivotPermutation1595; decide +kernel
  have hmoment : injectiveMoment H node1595 = injectiveMoment H pivotMatrix1595 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1595 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1595 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1595 (0 : Fin 4)) =
      Sparse.eval value1081 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1595 (0 : Fin 4) = raw2081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1595 raw2081; decide +kernel
    rw [heq]
    exact (canonical2081 hH).trans (sound1081 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1595 (1 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1595 (1 : Fin 4) = raw1705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1595 raw1705; decide +kernel
    rw [heq]
    exact (canonical1705 hH).trans (sound1080 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1595 (2 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1595 (2 : Fin 4) = raw1700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1595 raw1700; decide +kernel
    rw [heq]
    exact (canonical1700 hH).trans (sound464 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1595 (3 : Fin 4)) =
      Sparse.eval value786 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1595 (3 : Fin 4) = raw1699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1595 raw1699; decide +kernel
    rw [heq]
    exact (canonical1699 hH).trans (sound786 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1595 + (injectiveMoment H (mergeFirst pivotMatrix1595 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1595 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1595 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1595 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1595, value1080, value1081, value464, value786, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1596 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1596 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem sound1596 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1596 = Sparse.eval value1596 (momentVector H) := by
  have heq : pivotMatrix1596 = (fun u v => node1596 (pivotPermutation1596 u) v) := by apply Matrix.ext; unfold pivotMatrix1596 node1596 pivotPermutation1596; decide +kernel
  have hmoment : injectiveMoment H node1596 = injectiveMoment H pivotMatrix1596 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1596 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1596 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1596 (0 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1596 (0 : Fin 4) = raw2082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1596 raw2082; decide +kernel
    rw [heq]
    exact (canonical2082 hH).trans (sound490 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1596 (1 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1596 (1 : Fin 4) = raw1706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1596 raw1706; decide +kernel
    rw [heq]
    exact (canonical1706 hH).trans (sound467 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1596 (2 : Fin 4)) =
      Sparse.eval value465 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1596 (2 : Fin 4) = raw1701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1596 raw1701; decide +kernel
    rw [heq]
    exact (canonical1701 hH).trans (sound465 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1596 (3 : Fin 4)) =
      Sparse.eval value464 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1596 (3 : Fin 4) = raw1700 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1596 raw1700; decide +kernel
    rw [heq]
    exact (canonical1700 hH).trans (sound464 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1596 + (injectiveMoment H (mergeFirst pivotMatrix1596 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1596 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1596 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1596 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1596, value464, value465, value467, value490, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1597 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1597 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem sound1597 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1597 = Sparse.eval value1597 (momentVector H) := by
  have heq : pivotMatrix1597 = (fun u v => node1597 (pivotPermutation1597 u) v) := by apply Matrix.ext; unfold pivotMatrix1597 node1597 pivotPermutation1597; decide +kernel
  have hmoment : injectiveMoment H node1597 = injectiveMoment H pivotMatrix1597 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1597 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1597 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1597 (0 : Fin 4)) =
      Sparse.eval value1066 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1597 (0 : Fin 4) = raw2088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1597 raw2088; decide +kernel
    rw [heq]
    exact (canonical2088 hH).trans (sound1066 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1597 (1 : Fin 4)) =
      Sparse.eval value1071 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1597 (1 : Fin 4) = raw1709 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1597 raw1709; decide +kernel
    rw [heq]
    exact (canonical1709 hH).trans (sound1071 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1597 (2 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1597 (2 : Fin 4) = raw1706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1597 raw1706; decide +kernel
    rw [heq]
    exact (canonical1706 hH).trans (sound467 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1597 (3 : Fin 4)) =
      Sparse.eval value1080 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1597 (3 : Fin 4) = raw1705 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1597 raw1705; decide +kernel
    rw [heq]
    exact (canonical1705 hH).trans (sound1080 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1597 + (injectiveMoment H (mergeFirst pivotMatrix1597 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1597 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1597 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1597 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1597, value1066, value1071, value1080, value467, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1598 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1598 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound1598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1598 = Sparse.eval value1598 (momentVector H) := by
  have heq : pivotMatrix1598 = (fun u v => node1598 (pivotPermutation1598 u) v) := by apply Matrix.ext; unfold pivotMatrix1598 node1598 pivotPermutation1598; decide +kernel
  have hmoment : injectiveMoment H node1598 = injectiveMoment H pivotMatrix1598 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1598 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1598 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1598 (0 : Fin 4)) =
      Sparse.eval value1269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1598 (0 : Fin 4) = raw2099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1598 raw2099; decide +kernel
    rw [heq]
    exact (canonical2099 hH).trans (sound1269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1598 (1 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1598 (1 : Fin 4) = raw1715 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1598 raw1715; decide +kernel
    rw [heq]
    exact (canonical1715 hH).trans (sound1278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1598 (2 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1598 (2 : Fin 4) = raw1712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1598 raw1712; decide +kernel
    rw [heq]
    exact (canonical1712 hH).trans (sound468 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1598 (3 : Fin 4)) =
      Sparse.eval value1273 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1598 (3 : Fin 4) = raw1711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1598 raw1711; decide +kernel
    rw [heq]
    exact (canonical1711 hH).trans (sound1273 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1598 + (injectiveMoment H (mergeFirst pivotMatrix1598 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1598 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1598 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1598 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1598, value1269, value1273, value1278, value468, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1599 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1599 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound1599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1599 = Sparse.eval value1599 (momentVector H) := by
  have heq : pivotMatrix1599 = (fun u v => node1599 (pivotPermutation1599 u) v) := by apply Matrix.ext; unfold pivotMatrix1599 node1599 pivotPermutation1599; decide +kernel
  have hmoment : injectiveMoment H node1599 = injectiveMoment H pivotMatrix1599 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1599 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1599 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1599 (0 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (0 : Fin 4) = raw2100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw2100; decide +kernel
    rw [heq]
    exact (canonical2100 hH).trans (sound476 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1599 (1 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (1 : Fin 4) = raw1716 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw1716; decide +kernel
    rw [heq]
    exact (canonical1716 hH).trans (sound454 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1599 (2 : Fin 4)) =
      Sparse.eval value469 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (2 : Fin 4) = raw1713 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw1713; decide +kernel
    rw [heq]
    exact (canonical1713 hH).trans (sound469 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1599 (3 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1599 (3 : Fin 4) = raw1712 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1599 raw1712; decide +kernel
    rw [heq]
    exact (canonical1712 hH).trans (sound468 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1599 + (injectiveMoment H (mergeFirst pivotMatrix1599 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1599 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1599 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1599 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1599, value454, value468, value469, value476, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
