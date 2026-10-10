import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical248
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical283
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical288
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical315
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical316
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical317
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical318

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation1344 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, -2, 2, 1], ![1, 2, -2, -1]]

theorem sound1344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1344 = Sparse.eval value1344 (momentVector H) := by
  have heq : pivotMatrix1344 = (fun u v => node1344.transpose (pivotPermutation1344 u) v) := by apply Matrix.ext; unfold pivotMatrix1344 node1344 pivotPermutation1344; decide +kernel
  have hmoment : injectiveMoment H node1344 = injectiveMoment H pivotMatrix1344 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1344 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1344 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1344 (0 : Fin 3)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1344 (0 : Fin 3) = raw9699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1344 raw9699; decide +kernel
    rw [heq]
    exact (canonical9699 hH).trans (sound46 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1344 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1344 (1 : Fin 3) = raw10138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1344 raw10138; decide +kernel
    rw [heq]
    exact (canonical10138 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1344 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1344 (2 : Fin 3) = raw10140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1344 raw10140; decide +kernel
    rw [heq]
    exact (canonical10140 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1344 + (injectiveMoment H (mergeFirst pivotMatrix1344 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1344 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1344 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1344, value279, value291, value46, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1345 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1345 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3]]

theorem sound1345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1345 = Sparse.eval value1345 (momentVector H) := by
  have heq : pivotMatrix1345 = (fun u v => node1345 (pivotPermutation1345 u) v) := by apply Matrix.ext; unfold pivotMatrix1345 node1345 pivotPermutation1345; decide +kernel
  have hmoment : injectiveMoment H node1345 = injectiveMoment H pivotMatrix1345 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1345 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1345 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1345 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1345 (0 : Fin 3) = raw9230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1345 raw9230; decide +kernel
    rw [heq]
    exact (canonical9230 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1345 (1 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1345 (1 : Fin 3) = raw7874 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1345 raw7874; decide +kernel
    rw [heq]
    exact (canonical7874 hH).trans (sound259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1345 (2 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1345 (2 : Fin 3) = raw7848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1345 raw7848; decide +kernel
    rw [heq]
    exact (canonical7848 hH).trans (sound168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1345 + (injectiveMoment H (mergeFirst pivotMatrix1345 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1345 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1345 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1345, value10, value168, value259, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1346 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 1, 2], ![1, 2, -2, -1]]

theorem sound1346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1346 = Sparse.eval value1346 (momentVector H) := by
  have heq : pivotMatrix1346 = (fun u v => node1346.transpose (pivotPermutation1346 u) v) := by apply Matrix.ext; unfold pivotMatrix1346 node1346 pivotPermutation1346; decide +kernel
  have hmoment : injectiveMoment H node1346 = injectiveMoment H pivotMatrix1346 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1346 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1346 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1346 (0 : Fin 3)) =
      Sparse.eval value288 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1346 (0 : Fin 3) = raw9749 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1346 raw9749; decide +kernel
    rw [heq]
    exact (canonical9749 hH).trans (sound288 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1346 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1346 (1 : Fin 3) = raw10151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1346 raw10151; decide +kernel
    rw [heq]
    exact (canonical10151 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1346 (2 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1346 (2 : Fin 3) = raw10160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1346 raw10160; decide +kernel
    rw [heq]
    exact (canonical10160 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1346 + (injectiveMoment H (mergeFirst pivotMatrix1346 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1346 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1346 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1346, value184, value203, value288, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1347 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 2, 1], ![1, 2, -3, 0]]

theorem sound1347 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1347 = Sparse.eval value1347 (momentVector H) := by
  have heq : pivotMatrix1347 = (fun u v => node1347.transpose (pivotPermutation1347 u) v) := by apply Matrix.ext; unfold pivotMatrix1347 node1347 pivotPermutation1347; decide +kernel
  have hmoment : injectiveMoment H node1347 = injectiveMoment H pivotMatrix1347 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1347 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1347 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1347 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1347 (0 : Fin 3) = raw9750 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1347 raw9750; decide +kernel
    rw [heq]
    exact (canonical9750 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1347 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1347 (1 : Fin 3) = raw10152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1347 raw10152; decide +kernel
    rw [heq]
    exact (canonical10152 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1347 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1347 (2 : Fin 3) = raw10161 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1347 raw10161; decide +kernel
    rw [heq]
    exact (canonical10161 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1347 + (injectiveMoment H (mergeFirst pivotMatrix1347 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1347 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1347 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1347, value212, value226, value272, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1348 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 3, 0], ![1, 2, -4, 1]]

theorem sound1348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1348 = Sparse.eval value1348 (momentVector H) := by
  have heq : pivotMatrix1348 = (fun u v => node1348.transpose (pivotPermutation1348 u) v) := by apply Matrix.ext; unfold pivotMatrix1348 node1348 pivotPermutation1348; decide +kernel
  have hmoment : injectiveMoment H node1348 = injectiveMoment H pivotMatrix1348 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1348 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1348 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1348 (0 : Fin 3)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1348 (0 : Fin 3) = raw9751 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1348 raw9751; decide +kernel
    rw [heq]
    exact (canonical9751 hH).trans (sound254 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1348 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1348 (1 : Fin 3) = raw10153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1348 raw10153; decide +kernel
    rw [heq]
    exact (canonical10153 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1348 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1348 (2 : Fin 3) = raw10162 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1348 raw10162; decide +kernel
    rw [heq]
    exact (canonical10162 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1348 + (injectiveMoment H (mergeFirst pivotMatrix1348 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1348 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1348 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1348, value201, value225, value254, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1349 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1349 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

theorem sound1349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1349 = Sparse.eval value1349 (momentVector H) := by
  have heq : pivotMatrix1349 = (fun u v => node1349 (pivotPermutation1349 u) v) := by apply Matrix.ext; unfold pivotMatrix1349 node1349 pivotPermutation1349; decide +kernel
  have hmoment : injectiveMoment H node1349 = injectiveMoment H pivotMatrix1349 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1349 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1349 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1349 (0 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1349 (0 : Fin 3) = raw7823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1349 raw7823; decide +kernel
    rw [heq]
    exact (canonical7823 hH).trans (sound283 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1349 (1 : Fin 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1349 (1 : Fin 3) = raw7862 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1349 raw7862; decide +kernel
    rw [heq]
    exact (canonical7862 hH).trans (sound65 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1349 (2 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1349 (2 : Fin 3) = raw7866 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1349 raw7866; decide +kernel
    rw [heq]
    exact (canonical7866 hH).trans (sound293 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1349 + (injectiveMoment H (mergeFirst pivotMatrix1349 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1349 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1349 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1349, value283, value293, value65, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1350 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1350 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1]]

theorem sound1350 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1350 = Sparse.eval value1350 (momentVector H) := by
  have heq : pivotMatrix1350 = (fun u v => node1350 (pivotPermutation1350 u) v) := by apply Matrix.ext; unfold pivotMatrix1350 node1350 pivotPermutation1350; decide +kernel
  have hmoment : injectiveMoment H node1350 = injectiveMoment H pivotMatrix1350 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1350 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1350 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1350 (0 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1350 (0 : Fin 3) = raw7827 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1350 raw7827; decide +kernel
    rw [heq]
    exact (canonical7827 hH).trans (sound259 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1350 (1 : Fin 3)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1350 (1 : Fin 3) = raw7869 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1350 raw7869; decide +kernel
    rw [heq]
    exact (canonical7869 hH).trans (sound227 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1350 (2 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1350 (2 : Fin 3) = raw7872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1350 raw7872; decide +kernel
    rw [heq]
    exact (canonical7872 hH).trans (sound259 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1350 + (injectiveMoment H (mergeFirst pivotMatrix1350 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1350 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1350 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1350, value227, value259, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1351 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 2, 1, -2], ![1, -2, -2, 3]]

theorem sound1351 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1351 = Sparse.eval value1351 (momentVector H) := by
  have heq : pivotMatrix1351 = (fun u v => node1351.transpose (pivotPermutation1351 u) v) := by apply Matrix.ext; unfold pivotMatrix1351 node1351 pivotPermutation1351; decide +kernel
  have hmoment : injectiveMoment H node1351 = injectiveMoment H pivotMatrix1351 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1351 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1351 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1351 (0 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1351 (0 : Fin 3) = raw9758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1351 raw9758; decide +kernel
    rw [heq]
    exact (canonical9758 hH).trans (sound268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1351 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1351 (1 : Fin 3) = raw10154 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1351 raw10154; decide +kernel
    rw [heq]
    exact (canonical10154 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1351 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1351 (2 : Fin 3) = raw10163 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1351 raw10163; decide +kernel
    rw [heq]
    exact (canonical10163 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1351 + (injectiveMoment H (mergeFirst pivotMatrix1351 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1351 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1351 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1351, value153, value184, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1352 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1352 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 3, -2, 0], ![1, -3, 1, 1]]

theorem sound1352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1352 = Sparse.eval value1352 (momentVector H) := by
  have heq : pivotMatrix1352 = (fun u v => node1352.transpose (pivotPermutation1352 u) v) := by apply Matrix.ext; unfold pivotMatrix1352 node1352 pivotPermutation1352; decide +kernel
  have hmoment : injectiveMoment H node1352 = injectiveMoment H pivotMatrix1352 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1352 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1352 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1352 (0 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1352 (0 : Fin 3) = raw9759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1352 raw9759; decide +kernel
    rw [heq]
    exact (canonical9759 hH).trans (sound285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1352 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1352 (1 : Fin 3) = raw10155 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1352 raw10155; decide +kernel
    rw [heq]
    exact (canonical10155 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1352 (2 : Fin 3)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1352 (2 : Fin 3) = raw10164 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1352 raw10164; decide +kernel
    rw [heq]
    exact (canonical10164 hH).trans (sound215 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1352 + (injectiveMoment H (mergeFirst pivotMatrix1352 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1352 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1352 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1352, value215, value223, value285, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1353 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1353 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 4, -3, 0], ![1, -4, 2, 1]]

theorem sound1353 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1353 = Sparse.eval value1353 (momentVector H) := by
  have heq : pivotMatrix1353 = (fun u v => node1353.transpose (pivotPermutation1353 u) v) := by apply Matrix.ext; unfold pivotMatrix1353 node1353 pivotPermutation1353; decide +kernel
  have hmoment : injectiveMoment H node1353 = injectiveMoment H pivotMatrix1353 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1353 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1353 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1353 (0 : Fin 3)) =
      Sparse.eval value270 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1353 (0 : Fin 3) = raw9760 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1353 raw9760; decide +kernel
    rw [heq]
    exact (canonical9760 hH).trans (sound270 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1353 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1353 (1 : Fin 3) = raw10156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1353 raw10156; decide +kernel
    rw [heq]
    exact (canonical10156 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1353 (2 : Fin 3)) =
      Sparse.eval value217 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1353 (2 : Fin 3) = raw10165 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1353 raw10165; decide +kernel
    rw [heq]
    exact (canonical10165 hH).trans (sound217 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1353 + (injectiveMoment H (mergeFirst pivotMatrix1353 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1353 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1353 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1353, value217, value219, value270, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1354 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1354 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem sound1354 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1354 = Sparse.eval value1354 (momentVector H) := by
  have heq : pivotMatrix1354 = (fun u v => node1354 (pivotPermutation1354 u) v) := by apply Matrix.ext; unfold pivotMatrix1354 node1354 pivotPermutation1354; decide +kernel
  have hmoment : injectiveMoment H node1354 = injectiveMoment H pivotMatrix1354 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1354 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1354 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1354 (0 : Fin 3)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1354 (0 : Fin 3) = raw7121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1354 raw7121; decide +kernel
    rw [heq]
    exact (canonical7121 hH).trans (sound243 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1354 (1 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1354 (1 : Fin 3) = raw8294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1354 raw8294; decide +kernel
    rw [heq]
    exact (canonical8294 hH).trans (sound241 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1354 (2 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1354 (2 : Fin 3) = raw8305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1354 raw8305; decide +kernel
    rw [heq]
    exact (canonical8305 hH).trans (sound51 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1354 + (injectiveMoment H (mergeFirst pivotMatrix1354 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1354 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1354 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1354, value241, value243, value51, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1355 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem sound1355 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1355 = Sparse.eval value1355 (momentVector H) := by
  have heq : pivotMatrix1355 = (fun u v => node1355 (pivotPermutation1355 u) v) := by apply Matrix.ext; unfold pivotMatrix1355 node1355 pivotPermutation1355; decide +kernel
  have hmoment : injectiveMoment H node1355 = injectiveMoment H pivotMatrix1355 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1355 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1355 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1355 (0 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1355 (0 : Fin 3) = raw7787 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1355 raw7787; decide +kernel
    rw [heq]
    exact (canonical7787 hH).trans (sound222 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1355 (1 : Fin 3)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1355 (1 : Fin 3) = raw9065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1355 raw9065; decide +kernel
    rw [heq]
    exact (canonical9065 hH).trans (sound214 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1355 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1355 (2 : Fin 3) = raw9078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1355 raw9078; decide +kernel
    rw [heq]
    exact (canonical9078 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1355 + (injectiveMoment H (mergeFirst pivotMatrix1355 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1355 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1355 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1355, value214, value222, value58, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1356 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem sound1356 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1356 = Sparse.eval value1356 (momentVector H) := by
  have heq : pivotMatrix1356 = (fun u v => node1356 (pivotPermutation1356 u) v) := by apply Matrix.ext; unfold pivotMatrix1356 node1356 pivotPermutation1356; decide +kernel
  have hmoment : injectiveMoment H node1356 = injectiveMoment H pivotMatrix1356 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1356 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1356 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1356 (0 : Fin 3)) =
      Sparse.eval value221 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1356 (0 : Fin 3) = raw7788 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1356 raw7788; decide +kernel
    rw [heq]
    exact (canonical7788 hH).trans (sound221 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1356 (1 : Fin 3)) =
      Sparse.eval value195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1356 (1 : Fin 3) = raw9066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1356 raw9066; decide +kernel
    rw [heq]
    exact (canonical9066 hH).trans (sound195 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1356 (2 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1356 (2 : Fin 3) = raw9079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1356 raw9079; decide +kernel
    rw [heq]
    exact (canonical9079 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1356 + (injectiveMoment H (mergeFirst pivotMatrix1356 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1356 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1356 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1356, value195, value221, value53, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1357 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

theorem sound1357 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1357 = Sparse.eval value1357 (momentVector H) := by
  have heq : pivotMatrix1357 = (fun u v => node1357 (pivotPermutation1357 u) v) := by apply Matrix.ext; unfold pivotMatrix1357 node1357 pivotPermutation1357; decide +kernel
  have hmoment : injectiveMoment H node1357 = injectiveMoment H pivotMatrix1357 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1357 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1357 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1357 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1357 (0 : Fin 3) = raw7824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1357 raw7824; decide +kernel
    rw [heq]
    exact (canonical7824 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1357 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1357 (1 : Fin 3) = raw9088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1357 raw9088; decide +kernel
    rw [heq]
    exact (canonical9088 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1357 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1357 (2 : Fin 3) = raw9148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1357 raw9148; decide +kernel
    rw [heq]
    exact (canonical9148 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1357 + (injectiveMoment H (mergeFirst pivotMatrix1357 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1357 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1357 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1357, value291, value4, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1358 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1358 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 2, -1], ![1, 1, 1, -3], ![-1, 1, -3, 3]]

theorem sound1358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1358 = Sparse.eval value1358 (momentVector H) := by
  have heq : pivotMatrix1358 = (fun u v => node1358.transpose (pivotPermutation1358 u) v) := by apply Matrix.ext; unfold pivotMatrix1358 node1358 pivotPermutation1358; decide +kernel
  have hmoment : injectiveMoment H node1358 = injectiveMoment H pivotMatrix1358 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1358 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1358 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1358 (0 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1358 (0 : Fin 3) = raw8265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1358 raw8265; decide +kernel
    rw [heq]
    exact (canonical8265 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1358 (1 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1358 (1 : Fin 3) = raw10108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1358 raw10108; decide +kernel
    rw [heq]
    exact (canonical10108 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1358 (2 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1358 (2 : Fin 3) = raw10109 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1358 raw10109; decide +kernel
    rw [heq]
    exact (canonical10109 hH).trans (sound89 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1358 + (injectiveMoment H (mergeFirst pivotMatrix1358 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1358 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1358 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1358, value170, value180, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1359 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, -2, 2, -1], ![-1, 3, -3, 1]]

theorem sound1359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1359 = Sparse.eval value1359 (momentVector H) := by
  have heq : pivotMatrix1359 = (fun u v => node1359.transpose (pivotPermutation1359 u) v) := by apply Matrix.ext; unfold pivotMatrix1359 node1359 pivotPermutation1359; decide +kernel
  have hmoment : injectiveMoment H node1359 = injectiveMoment H pivotMatrix1359 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1359 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1359 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1359 (0 : Fin 3)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1359 (0 : Fin 3) = raw8880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1359 raw8880; decide +kernel
    rw [heq]
    exact (canonical8880 hH).trans (sound267 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1359 (1 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1359 (1 : Fin 3) = raw10129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1359 raw10129; decide +kernel
    rw [heq]
    exact (canonical10129 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1359 (2 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1359 (2 : Fin 3) = raw10132 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1359 raw10132; decide +kernel
    rw [heq]
    exact (canonical10132 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1359 + (injectiveMoment H (mergeFirst pivotMatrix1359 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1359 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1359 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1359, value168, value258, value267, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1360 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, -1, 1, -1], ![-1, 2, -2, 1]]

theorem sound1360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1360 = Sparse.eval value1360 (momentVector H) := by
  have heq : pivotMatrix1360 = (fun u v => node1360.transpose (pivotPermutation1360 u) v) := by apply Matrix.ext; unfold pivotMatrix1360 node1360 pivotPermutation1360; decide +kernel
  have hmoment : injectiveMoment H node1360 = injectiveMoment H pivotMatrix1360 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1360 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1360 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1360 (0 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1360 (0 : Fin 3) = raw8881 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1360 raw8881; decide +kernel
    rw [heq]
    exact (canonical8881 hH).trans (sound283 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1360 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1360 (1 : Fin 3) = raw10130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1360 raw10130; decide +kernel
    rw [heq]
    exact (canonical10130 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1360 (2 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1360 (2 : Fin 3) = raw10133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1360 raw10133; decide +kernel
    rw [heq]
    exact (canonical10133 hH).trans (sound275 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1360 + (injectiveMoment H (mergeFirst pivotMatrix1360 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1360 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1360 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1360, value275, value283, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1361 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1361 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, -1, 2, -2], ![-1, 2, -3, 2]]

theorem sound1361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1361 = Sparse.eval value1361 (momentVector H) := by
  have heq : pivotMatrix1361 = (fun u v => node1361.transpose (pivotPermutation1361 u) v) := by apply Matrix.ext; unfold pivotMatrix1361 node1361 pivotPermutation1361; decide +kernel
  have hmoment : injectiveMoment H node1361 = injectiveMoment H pivotMatrix1361 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1361 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1361 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1361 (0 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1361 (0 : Fin 3) = raw8882 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1361 raw8882; decide +kernel
    rw [heq]
    exact (canonical8882 hH).trans (sound268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1361 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1361 (1 : Fin 3) = raw10131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1361 raw10131; decide +kernel
    rw [heq]
    exact (canonical10131 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1361 (2 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1361 (2 : Fin 3) = raw10134 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1361 raw10134; decide +kernel
    rw [heq]
    exact (canonical10134 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1361 + (injectiveMoment H (mergeFirst pivotMatrix1361 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1361 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1361 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1361, value175, value258, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1362 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1362 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem sound1362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1362 = Sparse.eval value1362 (momentVector H) := by
  have heq : pivotMatrix1362 = (fun u v => node1362 (pivotPermutation1362 u) v) := by apply Matrix.ext; unfold pivotMatrix1362 node1362 pivotPermutation1362; decide +kernel
  have hmoment : injectiveMoment H node1362 = injectiveMoment H pivotMatrix1362 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1362 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1362 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1362 (0 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1362 (0 : Fin 3) = raw7507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1362 raw7507; decide +kernel
    rw [heq]
    exact (canonical7507 hH).trans (sound284 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1362 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1362 (1 : Fin 3) = raw7936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1362 raw7936; decide +kernel
    rw [heq]
    exact (canonical7936 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1362 (2 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1362 (2 : Fin 3) = raw7938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1362 raw7938; decide +kernel
    rw [heq]
    exact (canonical7938 hH).trans (sound175 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1362 + (injectiveMoment H (mergeFirst pivotMatrix1362 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1362 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1362 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1362, value175, value283, value284, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1363 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1363 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

theorem sound1363 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1363 = Sparse.eval value1363 (momentVector H) := by
  have heq : pivotMatrix1363 = (fun u v => node1363 (pivotPermutation1363 u) v) := by apply Matrix.ext; unfold pivotMatrix1363 node1363 pivotPermutation1363; decide +kernel
  have hmoment : injectiveMoment H node1363 = injectiveMoment H pivotMatrix1363 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1363 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1363 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1363 (0 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1363 (0 : Fin 3) = raw7508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1363 raw7508; decide +kernel
    rw [heq]
    exact (canonical7508 hH).trans (sound269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1363 (1 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1363 (1 : Fin 3) = raw7937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1363 raw7937; decide +kernel
    rw [heq]
    exact (canonical7937 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1363 (2 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1363 (2 : Fin 3) = raw7939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1363 raw7939; decide +kernel
    rw [heq]
    exact (canonical7939 hH).trans (sound241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1363 + (injectiveMoment H (mergeFirst pivotMatrix1363 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1363 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1363 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1363, value168, value241, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1364 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1364 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 2, -2], ![1, 2, 0, -3], ![-1, -1, -2, 4]]

theorem sound1364 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1364 = Sparse.eval value1364 (momentVector H) := by
  have heq : pivotMatrix1364 = (fun u v => node1364.transpose (pivotPermutation1364 u) v) := by apply Matrix.ext; unfold pivotMatrix1364 node1364 pivotPermutation1364; decide +kernel
  have hmoment : injectiveMoment H node1364 = injectiveMoment H pivotMatrix1364 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1364 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1364 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1364 (0 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1364 (0 : Fin 3) = raw8929 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1364 raw8929; decide +kernel
    rw [heq]
    exact (canonical8929 hH).trans (sound206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1364 (1 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1364 (1 : Fin 3) = raw10136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1364 raw10136; decide +kernel
    rw [heq]
    exact (canonical10136 hH).trans (sound146 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1364 (2 : Fin 3)) =
      Sparse.eval value74 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1364 (2 : Fin 3) = raw10137 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1364 raw10137; decide +kernel
    rw [heq]
    exact (canonical10137 hH).trans (sound74 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1364 + (injectiveMoment H (mergeFirst pivotMatrix1364 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1364 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1364 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1364, value146, value206, value74, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1365 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1365 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, -3, 2, 0], ![-1, 3, -3, 1]]

theorem sound1365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1365 = Sparse.eval value1365 (momentVector H) := by
  have heq : pivotMatrix1365 = (fun u v => node1365.transpose (pivotPermutation1365 u) v) := by apply Matrix.ext; unfold pivotMatrix1365 node1365 pivotPermutation1365; decide +kernel
  have hmoment : injectiveMoment H node1365 = injectiveMoment H pivotMatrix1365 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1365 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1365 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1365 (0 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1365 (0 : Fin 3) = raw9948 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1365 raw9948; decide +kernel
    rw [heq]
    exact (canonical9948 hH).trans (sound269 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1365 (1 : Fin 3)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1365 (1 : Fin 3) = raw10166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1365 raw10166; decide +kernel
    rw [heq]
    exact (canonical10166 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1365 (2 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1365 (2 : Fin 3) = raw10169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1365 raw10169; decide +kernel
    rw [heq]
    exact (canonical10169 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1365 + (injectiveMoment H (mergeFirst pivotMatrix1365 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1365 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1365 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1365, value196, value222, value269, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1366 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, -2, 2, -1], ![-1, 2, -3, 2]]

theorem sound1366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1366 = Sparse.eval value1366 (momentVector H) := by
  have heq : pivotMatrix1366 = (fun u v => node1366.transpose (pivotPermutation1366 u) v) := by apply Matrix.ext; unfold pivotMatrix1366 node1366 pivotPermutation1366; decide +kernel
  have hmoment : injectiveMoment H node1366 = injectiveMoment H pivotMatrix1366 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1366 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1366 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1366 (0 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1366 (0 : Fin 3) = raw9949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1366 raw9949; decide +kernel
    rw [heq]
    exact (canonical9949 hH).trans (sound268 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1366 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1366 (1 : Fin 3) = raw10167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1366 raw10167; decide +kernel
    rw [heq]
    exact (canonical10167 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1366 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1366 (2 : Fin 3) = raw10171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1366 raw10171; decide +kernel
    rw [heq]
    exact (canonical10171 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1366 + (injectiveMoment H (mergeFirst pivotMatrix1366 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1366 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1366 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1366, value167, value169, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1367 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1367 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

theorem sound1367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1367 = Sparse.eval value1367 (momentVector H) := by
  have heq : pivotMatrix1367 = (fun u v => node1367 (pivotPermutation1367 u) v) := by apply Matrix.ext; unfold pivotMatrix1367 node1367 pivotPermutation1367; decide +kernel
  have hmoment : injectiveMoment H node1367 = injectiveMoment H pivotMatrix1367 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1367 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1367 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1367 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1367 (0 : Fin 3) = raw7901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1367 raw7901; decide +kernel
    rw [heq]
    exact (canonical7901 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1367 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1367 (1 : Fin 3) = raw7938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1367 raw7938; decide +kernel
    rw [heq]
    exact (canonical7938 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1367 (2 : Fin 3)) =
      Sparse.eval value241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1367 (2 : Fin 3) = raw7939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1367 raw7939; decide +kernel
    rw [heq]
    exact (canonical7939 hH).trans (sound241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1367 + (injectiveMoment H (mergeFirst pivotMatrix1367 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1367 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1367 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1367, value175, value241, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1368 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1368 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![2, -1, 1, -2], ![-2, 2, -2, 2]]

theorem sound1368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1368 = Sparse.eval value1368 (momentVector H) := by
  have heq : pivotMatrix1368 = (fun u v => node1368.transpose (pivotPermutation1368 u) v) := by apply Matrix.ext; unfold pivotMatrix1368 node1368 pivotPermutation1368; decide +kernel
  have hmoment : injectiveMoment H node1368 = injectiveMoment H pivotMatrix1368 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1368 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1368 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1368 (0 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1368 (0 : Fin 3) = raw8883 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1368 raw8883; decide +kernel
    rw [heq]
    exact (canonical8883 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1368 (1 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1368 (1 : Fin 3) = raw10133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1368 raw10133; decide +kernel
    rw [heq]
    exact (canonical10133 hH).trans (sound275 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1368 (2 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1368 (2 : Fin 3) = raw10135 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1368 raw10135; decide +kernel
    rw [heq]
    exact (canonical10135 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1368 + (injectiveMoment H (mergeFirst pivotMatrix1368 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1368 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1368 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1368, value258, value275, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1369 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![2, -3, 1, 0], ![-2, 3, -2, 1]]

theorem sound1369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1369 = Sparse.eval value1369 (momentVector H) := by
  have heq : pivotMatrix1369 = (fun u v => node1369.transpose (pivotPermutation1369 u) v) := by apply Matrix.ext; unfold pivotMatrix1369 node1369 pivotPermutation1369; decide +kernel
  have hmoment : injectiveMoment H node1369 = injectiveMoment H pivotMatrix1369 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1369 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1369 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1369 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1369 (0 : Fin 3) = raw9950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1369 raw9950; decide +kernel
    rw [heq]
    exact (canonical9950 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1369 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1369 (1 : Fin 3) = raw10168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1369 raw10168; decide +kernel
    rw [heq]
    exact (canonical10168 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1369 (2 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1369 (2 : Fin 3) = raw10172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1369 raw10172; decide +kernel
    rw [heq]
    exact (canonical10172 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1369 + (injectiveMoment H (mergeFirst pivotMatrix1369 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1369 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1369 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1369, value196, value223, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1370 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![2, -2, 1, -1], ![-2, 2, -2, 2]]

theorem sound1370 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1370 = Sparse.eval value1370 (momentVector H) := by
  have heq : pivotMatrix1370 = (fun u v => node1370.transpose (pivotPermutation1370 u) v) := by apply Matrix.ext; unfold pivotMatrix1370 node1370 pivotPermutation1370; decide +kernel
  have hmoment : injectiveMoment H node1370 = injectiveMoment H pivotMatrix1370 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1370 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1370 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1370 (0 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1370 (0 : Fin 3) = raw9951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1370 raw9951; decide +kernel
    rw [heq]
    exact (canonical9951 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1370 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1370 (1 : Fin 3) = raw10170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1370 raw10170; decide +kernel
    rw [heq]
    exact (canonical10170 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1370 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1370 (2 : Fin 3) = raw10173 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1370 raw10173; decide +kernel
    rw [heq]
    exact (canonical10173 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1370 + (injectiveMoment H (mergeFirst pivotMatrix1370 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1370 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1370 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1370, value167, value202, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1371 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1371 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem sound1371 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1371 = Sparse.eval value1371 (momentVector H) := by
  have heq : pivotMatrix1371 = (fun u v => node1371 (pivotPermutation1371 u) v) := by apply Matrix.ext; unfold pivotMatrix1371 node1371 pivotPermutation1371; decide +kernel
  have hmoment : injectiveMoment H node1371 = injectiveMoment H pivotMatrix1371 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1371 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1371 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1371 (0 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1371 (0 : Fin 3) = raw7938 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1371 raw7938; decide +kernel
    rw [heq]
    exact (canonical7938 hH).trans (sound175 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1371 (1 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1371 (1 : Fin 3) = raw7950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1371 raw7950; decide +kernel
    rw [heq]
    exact (canonical7950 hH).trans (sound268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1371 (2 : Fin 3)) =
      Sparse.eval value144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1371 (2 : Fin 3) = raw7951 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1371 raw7951; decide +kernel
    rw [heq]
    exact (canonical7951 hH).trans (sound144 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1371 + (injectiveMoment H (mergeFirst pivotMatrix1371 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1371 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1371 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1371, value144, value175, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1372 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 1, 1, -3], ![2, -2, 1, -1], ![-2, 1, -2, 3]]

theorem sound1372 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1372 = Sparse.eval value1372 (momentVector H) := by
  have heq : pivotMatrix1372 = (fun u v => node1372.transpose (pivotPermutation1372 u) v) := by apply Matrix.ext; unfold pivotMatrix1372 node1372 pivotPermutation1372; decide +kernel
  have hmoment : injectiveMoment H node1372 = injectiveMoment H pivotMatrix1372 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1372 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1372 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1372 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1372 (0 : Fin 3) = raw10107 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1372 raw10107; decide +kernel
    rw [heq]
    exact (canonical10107 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1372 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1372 (1 : Fin 3) = raw10174 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1372 raw10174; decide +kernel
    rw [heq]
    exact (canonical10174 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1372 (2 : Fin 3)) =
      Sparse.eval value89 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1372 (2 : Fin 3) = raw10175 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1372 raw10175; decide +kernel
    rw [heq]
    exact (canonical10175 hH).trans (sound89 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1372 + (injectiveMoment H (mergeFirst pivotMatrix1372 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1372 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1372 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1372, value184, value223, value89, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1373 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -3, 4, 0], ![0, 3, -4, 1]]

theorem sound1373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1373 = Sparse.eval value1373 (momentVector H) := by
  have heq : pivotMatrix1373 = (fun u v => node1373.transpose (pivotPermutation1373 u) v) := by apply Matrix.ext; unfold pivotMatrix1373 node1373 pivotPermutation1373; decide +kernel
  have hmoment : injectiveMoment H node1373 = injectiveMoment H pivotMatrix1373 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1373 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1373 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1373 (0 : Fin 3)) =
      Sparse.eval value290 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1373 (0 : Fin 3) = raw10139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1373 raw10139; decide +kernel
    rw [heq]
    exact (canonical10139 hH).trans (sound290 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1373 (1 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1373 (1 : Fin 3) = raw10176 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1373 raw10176; decide +kernel
    rw [heq]
    exact (canonical10176 hH).trans (sound193 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1373 (2 : Fin 3)) =
      Sparse.eval value193 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1373 (2 : Fin 3) = raw10179 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1373 raw10179; decide +kernel
    rw [heq]
    exact (canonical10179 hH).trans (sound193 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1373 + (injectiveMoment H (mergeFirst pivotMatrix1373 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1373 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1373 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1373, value193, value290, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1374 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -2, 3, 0], ![0, 2, -3, 1]]

theorem sound1374 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1374 = Sparse.eval value1374 (momentVector H) := by
  have heq : pivotMatrix1374 = (fun u v => node1374.transpose (pivotPermutation1374 u) v) := by apply Matrix.ext; unfold pivotMatrix1374 node1374 pivotPermutation1374; decide +kernel
  have hmoment : injectiveMoment H node1374 = injectiveMoment H pivotMatrix1374 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1374 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1374 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1374 (0 : Fin 3)) =
      Sparse.eval value292 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1374 (0 : Fin 3) = raw10141 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1374 raw10141; decide +kernel
    rw [heq]
    exact (canonical10141 hH).trans (sound292 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1374 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1374 (1 : Fin 3) = raw10177 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1374 raw10177; decide +kernel
    rw [heq]
    exact (canonical10177 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1374 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1374 (2 : Fin 3) = raw10180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1374 raw10180; decide +kernel
    rw [heq]
    exact (canonical10180 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1374 + (injectiveMoment H (mergeFirst pivotMatrix1374 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1374 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1374 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1374, value198, value292, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1375 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, -3, 3, 0], ![-1, 3, -3, 1]]

theorem sound1375 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1375 = Sparse.eval value1375 (momentVector H) := by
  have heq : pivotMatrix1375 = (fun u v => node1375.transpose (pivotPermutation1375 u) v) := by apply Matrix.ext; unfold pivotMatrix1375 node1375 pivotPermutation1375; decide +kernel
  have hmoment : injectiveMoment H node1375 = injectiveMoment H pivotMatrix1375 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1375 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1375 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1375 (0 : Fin 3)) =
      Sparse.eval value289 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1375 (0 : Fin 3) = raw10142 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1375 raw10142; decide +kernel
    rw [heq]
    exact (canonical10142 hH).trans (sound289 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1375 (1 : Fin 3)) =
      Sparse.eval value220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1375 (1 : Fin 3) = raw10178 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1375 raw10178; decide +kernel
    rw [heq]
    exact (canonical10178 hH).trans (sound220 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1375 (2 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1375 (2 : Fin 3) = raw10181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1375 raw10181; decide +kernel
    rw [heq]
    exact (canonical10181 hH).trans (sound192 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1375 + (injectiveMoment H (mergeFirst pivotMatrix1375 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1375 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1375 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1375, value192, value220, value289, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1376 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -3, 2]]

theorem sound1376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1376 = Sparse.eval value1376 (momentVector H) := by
  have heq : pivotMatrix1376 = (fun u v => node1376.transpose (pivotPermutation1376 u) v) := by apply Matrix.ext; unfold pivotMatrix1376 node1376 pivotPermutation1376; decide +kernel
  have hmoment : injectiveMoment H node1376 = injectiveMoment H pivotMatrix1376 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1376 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1376 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1376 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1376 (0 : Fin 3) = raw10143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1376 raw10143; decide +kernel
    rw [heq]
    exact (canonical10143 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1376 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1376 (1 : Fin 3) = raw10180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1376 raw10180; decide +kernel
    rw [heq]
    exact (canonical10180 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1376 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1376 (2 : Fin 3) = raw10183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1376 raw10183; decide +kernel
    rw [heq]
    exact (canonical10183 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1376 + (injectiveMoment H (mergeFirst pivotMatrix1376 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1376 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1376 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1376, value163, value198, value280, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1377 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![1, -2, 2, -1], ![-2, 2, -2, 2]]

theorem sound1377 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1377 = Sparse.eval value1377 (momentVector H) := by
  have heq : pivotMatrix1377 = (fun u v => node1377.transpose (pivotPermutation1377 u) v) := by apply Matrix.ext; unfold pivotMatrix1377 node1377 pivotPermutation1377; decide +kernel
  have hmoment : injectiveMoment H node1377 = injectiveMoment H pivotMatrix1377 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1377 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1377 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1377 (0 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1377 (0 : Fin 3) = raw10144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1377 raw10144; decide +kernel
    rw [heq]
    exact (canonical10144 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1377 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1377 (1 : Fin 3) = raw10182 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1377 raw10182; decide +kernel
    rw [heq]
    exact (canonical10182 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1377 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1377 (2 : Fin 3) = raw10184 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1377 raw10184; decide +kernel
    rw [heq]
    exact (canonical10184 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1377 + (injectiveMoment H (mergeFirst pivotMatrix1377 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1377 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1377 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1377, value162, value197, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1378 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1378 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 2, 1, -2], ![0, 0, 2, -2], ![1, -2, -2, 3]]

theorem sound1378 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1378 = Sparse.eval value1378 (momentVector H) := by
  have heq : pivotMatrix1378 = (fun u v => node1378 (pivotPermutation1378 u) v) := by apply Matrix.ext; unfold pivotMatrix1378 node1378 pivotPermutation1378; decide +kernel
  have hmoment : injectiveMoment H node1378 = injectiveMoment H pivotMatrix1378 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1378 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1378 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1378 (0 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1378 (0 : Fin 3) = raw7973 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1378 raw7973; decide +kernel
    rw [heq]
    exact (canonical7973 hH).trans (sound169 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1378 (1 : Fin 3)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1378 (1 : Fin 3) = raw7975 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1378 raw7975; decide +kernel
    rw [heq]
    exact (canonical7975 hH).trans (sound268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1378 (2 : Fin 3)) =
      Sparse.eval value140 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1378 (2 : Fin 3) = raw7976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1378 raw7976; decide +kernel
    rw [heq]
    exact (canonical7976 hH).trans (sound140 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1378 + (injectiveMoment H (mergeFirst pivotMatrix1378 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1378 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1378 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1378, value140, value169, value268, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1379 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem sound1379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1379 = Sparse.eval value1379 (momentVector H) := by
  have heq : pivotMatrix1379 = (fun u v => node1379 (pivotPermutation1379 u) v) := by apply Matrix.ext; unfold pivotMatrix1379 node1379 pivotPermutation1379; decide +kernel
  have hmoment : injectiveMoment H node1379 = injectiveMoment H pivotMatrix1379 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1379 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1379 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1379 (0 : Fin 5)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1379 (0 : Fin 5) = raw282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1379 raw282; decide +kernel
    rw [heq]
    exact (canonical282 hH).trans (sound739 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1379 (1 : Fin 5)) =
      Sparse.eval value299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1379 (1 : Fin 5) = raw232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1379 raw232; decide +kernel
    rw [heq]
    exact (canonical232 hH).trans (sound299 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1379 (2 : Fin 5)) =
      Sparse.eval value299 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1379 (2 : Fin 5) = raw222 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1379 raw222; decide +kernel
    rw [heq]
    exact (canonical222 hH).trans (sound299 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1379 (3 : Fin 5)) =
      Sparse.eval value389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1379 (3 : Fin 5) = raw220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1379 raw220; decide +kernel
    rw [heq]
    exact (canonical220 hH).trans (sound389 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1379 (4 : Fin 5)) =
      Sparse.eval value297 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1379 (4 : Fin 5) = raw219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1379 raw219; decide +kernel
    rw [heq]
    exact (canonical219 hH).trans (sound297 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1379 + (injectiveMoment H (mergeFirst pivotMatrix1379 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1379 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1379 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1379 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1379 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1379, value297, value299, value389, value739, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1380 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem sound1380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1380 = Sparse.eval value1380 (momentVector H) := by
  have heq : pivotMatrix1380 = (fun u v => node1380 (pivotPermutation1380 u) v) := by apply Matrix.ext; unfold pivotMatrix1380 node1380 pivotPermutation1380; decide +kernel
  have hmoment : injectiveMoment H node1380 = injectiveMoment H pivotMatrix1380 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1380 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1380 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1380 (0 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1380 (0 : Fin 5) = raw283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1380 raw283; decide +kernel
    rw [heq]
    exact (canonical283 hH).trans (sound742 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1380 (1 : Fin 5)) =
      Sparse.eval value300 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1380 (1 : Fin 5) = raw233 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1380 raw233; decide +kernel
    rw [heq]
    exact (canonical233 hH).trans (sound300 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1380 (2 : Fin 5)) =
      Sparse.eval value300 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1380 (2 : Fin 5) = raw223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1380 raw223; decide +kernel
    rw [heq]
    exact (canonical223 hH).trans (sound300 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1380 (3 : Fin 5)) =
      Sparse.eval value298 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1380 (3 : Fin 5) = raw221 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1380 raw221; decide +kernel
    rw [heq]
    exact (canonical221 hH).trans (sound298 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1380 (4 : Fin 5)) =
      Sparse.eval value389 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1380 (4 : Fin 5) = raw220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1380 raw220; decide +kernel
    rw [heq]
    exact (canonical220 hH).trans (sound389 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1380 + (injectiveMoment H (mergeFirst pivotMatrix1380 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1380 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1380 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1380 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1380 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1380, value298, value300, value389, value742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1381 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem sound1381 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1381 = Sparse.eval value1381 (momentVector H) := by
  have heq : pivotMatrix1381 = (fun u v => node1381 (pivotPermutation1381 u) v) := by apply Matrix.ext; unfold pivotMatrix1381 node1381 pivotPermutation1381; decide +kernel
  have hmoment : injectiveMoment H node1381 = injectiveMoment H pivotMatrix1381 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1381 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1381 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1381 (0 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1381 (0 : Fin 5) = raw294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1381 raw294; decide +kernel
    rw [heq]
    exact (canonical294 hH).trans (sound737 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1381 (1 : Fin 5)) =
      Sparse.eval value303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1381 (1 : Fin 5) = raw234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1381 raw234; decide +kernel
    rw [heq]
    exact (canonical234 hH).trans (sound303 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1381 (2 : Fin 5)) =
      Sparse.eval value387 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1381 (2 : Fin 5) = raw228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1381 raw228; decide +kernel
    rw [heq]
    exact (canonical228 hH).trans (sound387 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1381 (3 : Fin 5)) =
      Sparse.eval value302 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1381 (3 : Fin 5) = raw226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1381 raw226; decide +kernel
    rw [heq]
    exact (canonical226 hH).trans (sound302 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1381 (4 : Fin 5)) =
      Sparse.eval value301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1381 (4 : Fin 5) = raw225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1381 raw225; decide +kernel
    rw [heq]
    exact (canonical225 hH).trans (sound301 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1381 + (injectiveMoment H (mergeFirst pivotMatrix1381 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1381 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1381 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1381 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1381 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1381, value301, value302, value303, value387, value737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1382 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem sound1382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1382 = Sparse.eval value1382 (momentVector H) := by
  have heq : pivotMatrix1382 = (fun u v => node1382 (pivotPermutation1382 u) v) := by apply Matrix.ext; unfold pivotMatrix1382 node1382 pivotPermutation1382; decide +kernel
  have hmoment : injectiveMoment H node1382 = injectiveMoment H pivotMatrix1382 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1382 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1382 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1382 (0 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1382 (0 : Fin 5) = raw306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1382 raw306; decide +kernel
    rw [heq]
    exact (canonical306 hH).trans (sound653 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1382 (1 : Fin 5)) =
      Sparse.eval value304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1382 (1 : Fin 5) = raw242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1382 raw242; decide +kernel
    rw [heq]
    exact (canonical242 hH).trans (sound304 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1382 (2 : Fin 5)) =
      Sparse.eval value384 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1382 (2 : Fin 5) = raw237 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1382 raw237; decide +kernel
    rw [heq]
    exact (canonical237 hH).trans (sound384 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1382 (3 : Fin 5)) =
      Sparse.eval value303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1382 (3 : Fin 5) = raw235 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1382 raw235; decide +kernel
    rw [heq]
    exact (canonical235 hH).trans (sound303 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1382 (4 : Fin 5)) =
      Sparse.eval value303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1382 (4 : Fin 5) = raw234 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1382 raw234; decide +kernel
    rw [heq]
    exact (canonical234 hH).trans (sound303 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1382 + (injectiveMoment H (mergeFirst pivotMatrix1382 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1382 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1382 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1382 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1382 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1382, value303, value304, value384, value653, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1383 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem sound1383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1383 = Sparse.eval value1383 (momentVector H) := by
  have heq : pivotMatrix1383 = (fun u v => node1383 (pivotPermutation1383 u) v) := by apply Matrix.ext; unfold pivotMatrix1383 node1383 pivotPermutation1383; decide +kernel
  have hmoment : injectiveMoment H node1383 = injectiveMoment H pivotMatrix1383 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1383 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1383 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1383 (0 : Fin 5)) =
      Sparse.eval value297 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1383 (0 : Fin 5) = raw219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1383 raw219; decide +kernel
    rw [heq]
    exact (canonical219 hH).trans (sound297 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1383 (1 : Fin 5)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1383 (1 : Fin 5) = raw275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1383 raw275; decide +kernel
    rw [heq]
    exact (canonical275 hH).trans (sound243 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1383 (2 : Fin 5)) =
      Sparse.eval value243 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1383 (2 : Fin 5) = raw280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1383 raw280; decide +kernel
    rw [heq]
    exact (canonical280 hH).trans (sound243 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1383 (3 : Fin 5)) =
      Sparse.eval value313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1383 (3 : Fin 5) = raw281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1383 raw281; decide +kernel
    rw [heq]
    exact (canonical281 hH).trans (sound313 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1383 (4 : Fin 5)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1383 (4 : Fin 5) = raw282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1383 raw282; decide +kernel
    rw [heq]
    exact (canonical282 hH).trans (sound739 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1383 + (injectiveMoment H (mergeFirst pivotMatrix1383 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1383 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1383 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1383 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1383 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1383, value243, value297, value313, value739, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1384 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem sound1384 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1384 = Sparse.eval value1384 (momentVector H) := by
  have heq : pivotMatrix1384 = (fun u v => node1384 (pivotPermutation1384 u) v) := by apply Matrix.ext; unfold pivotMatrix1384 node1384 pivotPermutation1384; decide +kernel
  have hmoment : injectiveMoment H node1384 = injectiveMoment H pivotMatrix1384 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1384 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1384 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1384 (0 : Fin 5)) =
      Sparse.eval value301 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1384 (0 : Fin 5) = raw225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1384 raw225; decide +kernel
    rw [heq]
    exact (canonical225 hH).trans (sound301 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1384 (1 : Fin 5)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1384 (1 : Fin 5) = raw277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1384 raw277; decide +kernel
    rw [heq]
    exact (canonical277 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1384 (2 : Fin 5)) =
      Sparse.eval value318 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1384 (2 : Fin 5) = raw290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1384 raw290; decide +kernel
    rw [heq]
    exact (canonical290 hH).trans (sound318 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1384 (3 : Fin 5)) =
      Sparse.eval value320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1384 (3 : Fin 5) = raw293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1384 raw293; decide +kernel
    rw [heq]
    exact (canonical293 hH).trans (sound320 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1384 (4 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1384 (4 : Fin 5) = raw294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1384 raw294; decide +kernel
    rw [heq]
    exact (canonical294 hH).trans (sound737 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1384 + (injectiveMoment H (mergeFirst pivotMatrix1384 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1384 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1384 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1384 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1384 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1384, value173, value301, value318, value320, value737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1385 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem sound1385 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1385 = Sparse.eval value1385 (momentVector H) := by
  have heq : pivotMatrix1385 = (fun u v => node1385 (pivotPermutation1385 u) v) := by apply Matrix.ext; unfold pivotMatrix1385 node1385 pivotPermutation1385; decide +kernel
  have hmoment : injectiveMoment H node1385 = injectiveMoment H pivotMatrix1385 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1385 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1385 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1385 (0 : Fin 5)) =
      Sparse.eval value304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1385 (0 : Fin 5) = raw242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1385 raw242; decide +kernel
    rw [heq]
    exact (canonical242 hH).trans (sound304 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1385 (1 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1385 (1 : Fin 5) = raw306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1385 raw306; decide +kernel
    rw [heq]
    exact (canonical306 hH).trans (sound653 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1385 (2 : Fin 5)) =
      Sparse.eval value323 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1385 (2 : Fin 5) = raw313 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1385 raw313; decide +kernel
    rw [heq]
    exact (canonical313 hH).trans (sound323 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1385 (3 : Fin 5)) =
      Sparse.eval value324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1385 (3 : Fin 5) = raw315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1385 raw315; decide +kernel
    rw [heq]
    exact (canonical315 hH).trans (sound324 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1385 (4 : Fin 5)) =
      Sparse.eval value324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1385 (4 : Fin 5) = raw316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1385 raw316; decide +kernel
    rw [heq]
    exact (canonical316 hH).trans (sound324 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1385 + (injectiveMoment H (mergeFirst pivotMatrix1385 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1385 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1385 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1385 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1385 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1385, value304, value323, value324, value653, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1386 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem sound1386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1386 = Sparse.eval value1386 (momentVector H) := by
  have heq : pivotMatrix1386 = (fun u v => node1386 (pivotPermutation1386 u) v) := by apply Matrix.ext; unfold pivotMatrix1386 node1386 pivotPermutation1386; decide +kernel
  have hmoment : injectiveMoment H node1386 = injectiveMoment H pivotMatrix1386 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1386 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1386 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1386 (0 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1386 (0 : Fin 5) = raw517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1386 raw517; decide +kernel
    rw [heq]
    exact (canonical517 hH).trans (sound699 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1386 (1 : Fin 5)) =
      Sparse.eval value315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1386 (1 : Fin 5) = raw299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1386 raw299; decide +kernel
    rw [heq]
    exact (canonical299 hH).trans (sound315 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1386 (2 : Fin 5)) =
      Sparse.eval value315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1386 (2 : Fin 5) = raw286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1386 raw286; decide +kernel
    rw [heq]
    exact (canonical286 hH).trans (sound315 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1386 (3 : Fin 5)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1386 (3 : Fin 5) = raw282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1386 raw282; decide +kernel
    rw [heq]
    exact (canonical282 hH).trans (sound739 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1386 (4 : Fin 5)) =
      Sparse.eval value313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1386 (4 : Fin 5) = raw281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1386 raw281; decide +kernel
    rw [heq]
    exact (canonical281 hH).trans (sound313 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1386 + (injectiveMoment H (mergeFirst pivotMatrix1386 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1386 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1386 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1386 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1386 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1386, value313, value315, value699, value739, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1387 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem sound1387 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1387 = Sparse.eval value1387 (momentVector H) := by
  have heq : pivotMatrix1387 = (fun u v => node1387 (pivotPermutation1387 u) v) := by apply Matrix.ext; unfold pivotMatrix1387 node1387 pivotPermutation1387; decide +kernel
  have hmoment : injectiveMoment H node1387 = injectiveMoment H pivotMatrix1387 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1387 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1387 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1387 (0 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1387 (0 : Fin 5) = raw519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1387 raw519; decide +kernel
    rw [heq]
    exact (canonical519 hH).trans (sound1139 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1387 (1 : Fin 5)) =
      Sparse.eval value316 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1387 (1 : Fin 5) = raw300 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1387 raw300; decide +kernel
    rw [heq]
    exact (canonical300 hH).trans (sound316 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1387 (2 : Fin 5)) =
      Sparse.eval value316 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1387 (2 : Fin 5) = raw287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1387 raw287; decide +kernel
    rw [heq]
    exact (canonical287 hH).trans (sound316 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1387 (3 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1387 (3 : Fin 5) = raw283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1387 raw283; decide +kernel
    rw [heq]
    exact (canonical283 hH).trans (sound742 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1387 (4 : Fin 5)) =
      Sparse.eval value739 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1387 (4 : Fin 5) = raw282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1387 raw282; decide +kernel
    rw [heq]
    exact (canonical282 hH).trans (sound739 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1387 + (injectiveMoment H (mergeFirst pivotMatrix1387 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1387 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1387 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1387 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1387 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1387, value1139, value316, value739, value742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1388 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem sound1388 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1388 = Sparse.eval value1388 (momentVector H) := by
  have heq : pivotMatrix1388 = (fun u v => node1388 (pivotPermutation1388 u) v) := by apply Matrix.ext; unfold pivotMatrix1388 node1388 pivotPermutation1388; decide +kernel
  have hmoment : injectiveMoment H node1388 = injectiveMoment H pivotMatrix1388 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1388 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1388 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1388 (0 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1388 (0 : Fin 5) = raw520 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1388 raw520; decide +kernel
    rw [heq]
    exact (canonical520 hH).trans (sound663 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1388 (1 : Fin 5)) =
      Sparse.eval value317 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1388 (1 : Fin 5) = raw301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1388 raw301; decide +kernel
    rw [heq]
    exact (canonical301 hH).trans (sound317 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1388 (2 : Fin 5)) =
      Sparse.eval value317 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1388 (2 : Fin 5) = raw288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1388 raw288; decide +kernel
    rw [heq]
    exact (canonical288 hH).trans (sound317 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1388 (3 : Fin 5)) =
      Sparse.eval value314 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1388 (3 : Fin 5) = raw284 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1388 raw284; decide +kernel
    rw [heq]
    exact (canonical284 hH).trans (sound314 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1388 (4 : Fin 5)) =
      Sparse.eval value742 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1388 (4 : Fin 5) = raw283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1388 raw283; decide +kernel
    rw [heq]
    exact (canonical283 hH).trans (sound742 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1388 + (injectiveMoment H (mergeFirst pivotMatrix1388 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1388 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1388 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1388 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1388 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1388, value314, value317, value663, value742, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1389 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem sound1389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1389 = Sparse.eval value1389 (momentVector H) := by
  have heq : pivotMatrix1389 = (fun u v => node1389 (pivotPermutation1389 u) v) := by apply Matrix.ext; unfold pivotMatrix1389 node1389 pivotPermutation1389; decide +kernel
  have hmoment : injectiveMoment H node1389 = injectiveMoment H pivotMatrix1389 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1389 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1389 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1389 (0 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1389 (0 : Fin 5) = raw531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1389 raw531; decide +kernel
    rw [heq]
    exact (canonical531 hH).trans (sound697 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1389 (1 : Fin 5)) =
      Sparse.eval value321 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1389 (1 : Fin 5) = raw303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1389 raw303; decide +kernel
    rw [heq]
    exact (canonical303 hH).trans (sound321 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1389 (2 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1389 (2 : Fin 5) = raw294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1389 raw294; decide +kernel
    rw [heq]
    exact (canonical294 hH).trans (sound737 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1389 (3 : Fin 5)) =
      Sparse.eval value319 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1389 (3 : Fin 5) = raw291 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1389 raw291; decide +kernel
    rw [heq]
    exact (canonical291 hH).trans (sound319 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1389 (4 : Fin 5)) =
      Sparse.eval value318 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1389 (4 : Fin 5) = raw290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1389 raw290; decide +kernel
    rw [heq]
    exact (canonical290 hH).trans (sound318 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1389 + (injectiveMoment H (mergeFirst pivotMatrix1389 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1389 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1389 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1389 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1389 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1389, value318, value319, value321, value697, value737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1390 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem sound1390 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1390 = Sparse.eval value1390 (momentVector H) := by
  have heq : pivotMatrix1390 = (fun u v => node1390 (pivotPermutation1390 u) v) := by apply Matrix.ext; unfold pivotMatrix1390 node1390 pivotPermutation1390; decide +kernel
  have hmoment : injectiveMoment H node1390 = injectiveMoment H pivotMatrix1390 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1390 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1390 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1390 (0 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1390 (0 : Fin 5) = raw534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1390 raw534; decide +kernel
    rw [heq]
    exact (canonical534 hH).trans (sound1139 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1390 (1 : Fin 5)) =
      Sparse.eval value322 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1390 (1 : Fin 5) = raw305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1390 raw305; decide +kernel
    rw [heq]
    exact (canonical305 hH).trans (sound322 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1390 (2 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1390 (2 : Fin 5) = raw296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1390 raw296; decide +kernel
    rw [heq]
    exact (canonical296 hH).trans (sound737 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1390 (3 : Fin 5)) =
      Sparse.eval value737 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1390 (3 : Fin 5) = raw294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1390 raw294; decide +kernel
    rw [heq]
    exact (canonical294 hH).trans (sound737 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1390 (4 : Fin 5)) =
      Sparse.eval value320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1390 (4 : Fin 5) = raw293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1390 raw293; decide +kernel
    rw [heq]
    exact (canonical293 hH).trans (sound320 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1390 + (injectiveMoment H (mergeFirst pivotMatrix1390 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1390 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1390 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1390 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1390 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1390, value1139, value320, value322, value737, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1391 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem sound1391 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1391 = Sparse.eval value1391 (momentVector H) := by
  have heq : pivotMatrix1391 = (fun u v => node1391 (pivotPermutation1391 u) v) := by apply Matrix.ext; unfold pivotMatrix1391 node1391 pivotPermutation1391; decide +kernel
  have hmoment : injectiveMoment H node1391 = injectiveMoment H pivotMatrix1391 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1391 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1391 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1391 (0 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1391 (0 : Fin 5) = raw551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1391 raw551; decide +kernel
    rw [heq]
    exact (canonical551 hH).trans (sound663 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1391 (1 : Fin 5)) =
      Sparse.eval value324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1391 (1 : Fin 5) = raw315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1391 raw315; decide +kernel
    rw [heq]
    exact (canonical315 hH).trans (sound324 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1391 (2 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1391 (2 : Fin 5) = raw308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1391 raw308; decide +kernel
    rw [heq]
    exact (canonical308 hH).trans (sound653 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1391 (3 : Fin 5)) =
      Sparse.eval value653 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1391 (3 : Fin 5) = raw306 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1391 raw306; decide +kernel
    rw [heq]
    exact (canonical306 hH).trans (sound653 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1391 (4 : Fin 5)) =
      Sparse.eval value322 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1391 (4 : Fin 5) = raw305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1391 raw305; decide +kernel
    rw [heq]
    exact (canonical305 hH).trans (sound322 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1391 + (injectiveMoment H (mergeFirst pivotMatrix1391 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1391 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1391 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1391 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1391 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1391, value322, value324, value653, value663, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1392 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem sound1392 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1392 = Sparse.eval value1392 (momentVector H) := by
  have heq : pivotMatrix1392 = (fun u v => node1392 (pivotPermutation1392 u) v) := by apply Matrix.ext; unfold pivotMatrix1392 node1392 pivotPermutation1392; decide +kernel
  have hmoment : injectiveMoment H node1392 = injectiveMoment H pivotMatrix1392 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1392 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1392 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1392 (0 : Fin 5)) =
      Sparse.eval value355 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1392 (0 : Fin 5) = raw695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1392 raw695; decide +kernel
    rw [heq]
    exact (canonical695 hH).trans (sound355 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1392 (1 : Fin 5)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1392 (1 : Fin 5) = raw493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1392 raw493; decide +kernel
    rw [heq]
    exact (canonical493 hH).trans (sound864 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1392 (2 : Fin 5)) =
      Sparse.eval value328 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1392 (2 : Fin 5) = raw467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1392 raw467; decide +kernel
    rw [heq]
    exact (canonical467 hH).trans (sound328 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1392 (3 : Fin 5)) =
      Sparse.eval value633 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1392 (3 : Fin 5) = raw464 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1392 raw464; decide +kernel
    rw [heq]
    exact (canonical464 hH).trans (sound633 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1392 (4 : Fin 5)) =
      Sparse.eval value326 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1392 (4 : Fin 5) = raw463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1392 raw463; decide +kernel
    rw [heq]
    exact (canonical463 hH).trans (sound326 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1392 + (injectiveMoment H (mergeFirst pivotMatrix1392 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1392 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1392 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1392 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1392 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1392, value326, value328, value355, value633, value864, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1393 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem sound1393 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1393 = Sparse.eval value1393 (momentVector H) := by
  have heq : pivotMatrix1393 = (fun u v => node1393 (pivotPermutation1393 u) v) := by apply Matrix.ext; unfold pivotMatrix1393 node1393 pivotPermutation1393; decide +kernel
  have hmoment : injectiveMoment H node1393 = injectiveMoment H pivotMatrix1393 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1393 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1393 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1393 (0 : Fin 5)) =
      Sparse.eval value356 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1393 (0 : Fin 5) = raw698 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1393 raw698; decide +kernel
    rw [heq]
    exact (canonical698 hH).trans (sound356 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1393 (1 : Fin 5)) =
      Sparse.eval value1138 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1393 (1 : Fin 5) = raw494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1393 raw494; decide +kernel
    rw [heq]
    exact (canonical494 hH).trans (sound1138 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1393 (2 : Fin 5)) =
      Sparse.eval value329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1393 (2 : Fin 5) = raw469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1393 raw469; decide +kernel
    rw [heq]
    exact (canonical469 hH).trans (sound329 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1393 (3 : Fin 5)) =
      Sparse.eval value327 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1393 (3 : Fin 5) = raw466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1393 raw466; decide +kernel
    rw [heq]
    exact (canonical466 hH).trans (sound327 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1393 (4 : Fin 5)) =
      Sparse.eval value635 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1393 (4 : Fin 5) = raw465 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1393 raw465; decide +kernel
    rw [heq]
    exact (canonical465 hH).trans (sound635 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1393 + (injectiveMoment H (mergeFirst pivotMatrix1393 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1393 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1393 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1393 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1393 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1393, value1138, value327, value329, value356, value635, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1394 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1394 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem sound1394 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1394 = Sparse.eval value1394 (momentVector H) := by
  have heq : pivotMatrix1394 = (fun u v => node1394 (pivotPermutation1394 u) v) := by apply Matrix.ext; unfold pivotMatrix1394 node1394 pivotPermutation1394; decide +kernel
  have hmoment : injectiveMoment H node1394 = injectiveMoment H pivotMatrix1394 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1394 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1394 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1394 (0 : Fin 5)) =
      Sparse.eval value357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1394 (0 : Fin 5) = raw701 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1394 raw701; decide +kernel
    rw [heq]
    exact (canonical701 hH).trans (sound357 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1394 (1 : Fin 5)) =
      Sparse.eval value648 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1394 (1 : Fin 5) = raw496 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1394 raw496; decide +kernel
    rw [heq]
    exact (canonical496 hH).trans (sound648 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1394 (2 : Fin 5)) =
      Sparse.eval value330 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1394 (2 : Fin 5) = raw472 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1394 raw472; decide +kernel
    rw [heq]
    exact (canonical472 hH).trans (sound330 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1394 (3 : Fin 5)) =
      Sparse.eval value631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1394 (3 : Fin 5) = raw468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1394 raw468; decide +kernel
    rw [heq]
    exact (canonical468 hH).trans (sound631 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1394 (4 : Fin 5)) =
      Sparse.eval value328 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1394 (4 : Fin 5) = raw467 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1394 raw467; decide +kernel
    rw [heq]
    exact (canonical467 hH).trans (sound328 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1394 + (injectiveMoment H (mergeFirst pivotMatrix1394 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1394 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1394 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1394 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1394 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1394, value328, value330, value357, value631, value648, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1395 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem sound1395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1395 = Sparse.eval value1395 (momentVector H) := by
  have heq : pivotMatrix1395 = (fun u v => node1395 (pivotPermutation1395 u) v) := by apply Matrix.ext; unfold pivotMatrix1395 node1395 pivotPermutation1395; decide +kernel
  have hmoment : injectiveMoment H node1395 = injectiveMoment H pivotMatrix1395 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1395 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1395 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1395 (0 : Fin 5)) =
      Sparse.eval value360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1395 (0 : Fin 5) = raw706 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1395 raw706; decide +kernel
    rw [heq]
    exact (canonical706 hH).trans (sound360 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1395 (1 : Fin 5)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1395 (1 : Fin 5) = raw504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1395 raw504; decide +kernel
    rw [heq]
    exact (canonical504 hH).trans (sound563 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1395 (2 : Fin 5)) =
      Sparse.eval value551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1395 (2 : Fin 5) = raw479 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1395 raw479; decide +kernel
    rw [heq]
    exact (canonical479 hH).trans (sound551 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1395 (3 : Fin 5)) =
      Sparse.eval value332 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1395 (3 : Fin 5) = raw477 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1395 raw477; decide +kernel
    rw [heq]
    exact (canonical477 hH).trans (sound332 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1395 (4 : Fin 5)) =
      Sparse.eval value309 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1395 (4 : Fin 5) = raw476 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1395 raw476; decide +kernel
    rw [heq]
    exact (canonical476 hH).trans (sound309 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1395 + (injectiveMoment H (mergeFirst pivotMatrix1395 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1395 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1395 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1395 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1395 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1395, value309, value332, value360, value551, value563, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1396 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1396 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem sound1396 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1396 = Sparse.eval value1396 (momentVector H) := by
  have heq : pivotMatrix1396 = (fun u v => node1396 (pivotPermutation1396 u) v) := by apply Matrix.ext; unfold pivotMatrix1396 node1396 pivotPermutation1396; decide +kernel
  have hmoment : injectiveMoment H node1396 = injectiveMoment H pivotMatrix1396 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1396 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1396 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1396 (0 : Fin 5)) =
      Sparse.eval value547 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1396 (0 : Fin 5) = raw2717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1396 raw2717; decide +kernel
    rw [heq]
    exact (canonical2717 hH).trans (sound547 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1396 (1 : Fin 5)) =
      Sparse.eval value350 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1396 (1 : Fin 5) = raw566 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1396 raw566; decide +kernel
    rw [heq]
    exact (canonical566 hH).trans (sound350 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1396 (2 : Fin 5)) =
      Sparse.eval value634 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1396 (2 : Fin 5) = raw481 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1396 raw481; decide +kernel
    rw [heq]
    exact (canonical481 hH).trans (sound634 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1396 (3 : Fin 5)) =
      Sparse.eval value329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1396 (3 : Fin 5) = raw470 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1396 raw470; decide +kernel
    rw [heq]
    exact (canonical470 hH).trans (sound329 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1396 (4 : Fin 5)) =
      Sparse.eval value631 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1396 (4 : Fin 5) = raw468 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1396 raw468; decide +kernel
    rw [heq]
    exact (canonical468 hH).trans (sound631 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1396 + (injectiveMoment H (mergeFirst pivotMatrix1396 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1396 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1396 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1396 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1396 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1396, value329, value350, value547, value631, value634, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1397 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem sound1397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1397 = Sparse.eval value1397 (momentVector H) := by
  have heq : pivotMatrix1397 = (fun u v => node1397 (pivotPermutation1397 u) v) := by apply Matrix.ext; unfold pivotMatrix1397 node1397 pivotPermutation1397; decide +kernel
  have hmoment : injectiveMoment H node1397 = injectiveMoment H pivotMatrix1397 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1397 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1397 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1397 (0 : Fin 5)) =
      Sparse.eval value549 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1397 (0 : Fin 5) = raw2720 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1397 raw2720; decide +kernel
    rw [heq]
    exact (canonical2720 hH).trans (sound549 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1397 (1 : Fin 5)) =
      Sparse.eval value333 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1397 (1 : Fin 5) = raw568 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1397 raw568; decide +kernel
    rw [heq]
    exact (canonical568 hH).trans (sound333 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1397 (2 : Fin 5)) =
      Sparse.eval value551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1397 (2 : Fin 5) = raw483 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1397 raw483; decide +kernel
    rw [heq]
    exact (canonical483 hH).trans (sound551 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1397 (3 : Fin 5)) =
      Sparse.eval value331 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1397 (3 : Fin 5) = raw474 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1397 raw474; decide +kernel
    rw [heq]
    exact (canonical474 hH).trans (sound331 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1397 (4 : Fin 5)) =
      Sparse.eval value331 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1397 (4 : Fin 5) = raw473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1397 raw473; decide +kernel
    rw [heq]
    exact (canonical473 hH).trans (sound331 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1397 + (injectiveMoment H (mergeFirst pivotMatrix1397 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1397 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1397 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1397 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1397 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1397, value331, value333, value549, value551, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1398 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1398 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem sound1398 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1398 = Sparse.eval value1398 (momentVector H) := by
  have heq : pivotMatrix1398 = (fun u v => node1398 (pivotPermutation1398 u) v) := by apply Matrix.ext; unfold pivotMatrix1398 node1398 pivotPermutation1398; decide +kernel
  have hmoment : injectiveMoment H node1398 = injectiveMoment H pivotMatrix1398 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1398 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1398 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1398 (0 : Fin 5)) =
      Sparse.eval value305 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1398 (0 : Fin 5) = raw269 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1398 raw269; decide +kernel
    rw [heq]
    exact (canonical269 hH).trans (sound305 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1398 (1 : Fin 5)) =
      Sparse.eval value325 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1398 (1 : Fin 5) = raw462 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1398 raw462; decide +kernel
    rw [heq]
    exact (canonical462 hH).trans (sound325 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1398 (2 : Fin 5)) =
      Sparse.eval value214 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1398 (2 : Fin 5) = raw487 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1398 raw487; decide +kernel
    rw [heq]
    exact (canonical487 hH).trans (sound214 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1398 (3 : Fin 5)) =
      Sparse.eval value1287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1398 (3 : Fin 5) = raw490 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1398 raw490; decide +kernel
    rw [heq]
    exact (canonical490 hH).trans (sound1287 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1398 (4 : Fin 5)) =
      Sparse.eval value334 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1398 (4 : Fin 5) = raw491 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1398 raw491; decide +kernel
    rw [heq]
    exact (canonical491 hH).trans (sound334 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1398 + (injectiveMoment H (mergeFirst pivotMatrix1398 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1398 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1398 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1398 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1398 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1398, value1287, value214, value305, value325, value334, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1399 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem sound1399 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1399 = Sparse.eval value1399 (momentVector H) := by
  have heq : pivotMatrix1399 = (fun u v => node1399 (pivotPermutation1399 u) v) := by apply Matrix.ext; unfold pivotMatrix1399 node1399 pivotPermutation1399; decide +kernel
  have hmoment : injectiveMoment H node1399 = injectiveMoment H pivotMatrix1399 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1399 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1399 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1399 (0 : Fin 5)) =
      Sparse.eval value306 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1399 (0 : Fin 5) = raw270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1399 raw270; decide +kernel
    rw [heq]
    exact (canonical270 hH).trans (sound306 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1399 (1 : Fin 5)) =
      Sparse.eval value326 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1399 (1 : Fin 5) = raw463 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1399 raw463; decide +kernel
    rw [heq]
    exact (canonical463 hH).trans (sound326 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1399 (2 : Fin 5)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1399 (2 : Fin 5) = raw488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1399 raw488; decide +kernel
    rw [heq]
    exact (canonical488 hH).trans (sound155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1399 (3 : Fin 5)) =
      Sparse.eval value335 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1399 (3 : Fin 5) = raw492 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1399 raw492; decide +kernel
    rw [heq]
    exact (canonical492 hH).trans (sound335 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1399 (4 : Fin 5)) =
      Sparse.eval value864 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1399 (4 : Fin 5) = raw493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1399 raw493; decide +kernel
    rw [heq]
    exact (canonical493 hH).trans (sound864 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1399 + (injectiveMoment H (mergeFirst pivotMatrix1399 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1399 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1399 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1399 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1399 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1399, value155, value306, value326, value335, value864, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1400 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1400 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem sound1400 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1400 = Sparse.eval value1400 (momentVector H) := by
  have heq : pivotMatrix1400 = (fun u v => node1400 (pivotPermutation1400 u) v) := by apply Matrix.ext; unfold pivotMatrix1400 node1400 pivotPermutation1400; decide +kernel
  have hmoment : injectiveMoment H node1400 = injectiveMoment H pivotMatrix1400 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1400 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1400 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1400 (0 : Fin 5)) =
      Sparse.eval value307 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1400 (0 : Fin 5) = raw271 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1400 raw271; decide +kernel
    rw [heq]
    exact (canonical271 hH).trans (sound307 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1400 (1 : Fin 5)) =
      Sparse.eval value327 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1400 (1 : Fin 5) = raw466 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1400 raw466; decide +kernel
    rw [heq]
    exact (canonical466 hH).trans (sound327 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1400 (2 : Fin 5)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1400 (2 : Fin 5) = raw489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1400 raw489; decide +kernel
    rw [heq]
    exact (canonical489 hH).trans (sound187 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1400 (3 : Fin 5)) =
      Sparse.eval value1138 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1400 (3 : Fin 5) = raw494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1400 raw494; decide +kernel
    rw [heq]
    exact (canonical494 hH).trans (sound1138 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1400 (4 : Fin 5)) =
      Sparse.eval value336 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1400 (4 : Fin 5) = raw495 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1400 raw495; decide +kernel
    rw [heq]
    exact (canonical495 hH).trans (sound336 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1400 + (injectiveMoment H (mergeFirst pivotMatrix1400 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1400 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1400 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1400 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1400 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1400, value1138, value187, value307, value327, value336, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1401 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem sound1401 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1401 = Sparse.eval value1401 (momentVector H) := by
  have heq : pivotMatrix1401 = (fun u v => node1401 (pivotPermutation1401 u) v) := by apply Matrix.ext; unfold pivotMatrix1401 node1401 pivotPermutation1401; decide +kernel
  have hmoment : injectiveMoment H node1401 = injectiveMoment H pivotMatrix1401 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1401 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1401 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1401 (0 : Fin 5)) =
      Sparse.eval value308 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1401 (0 : Fin 5) = raw272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1401 raw272; decide +kernel
    rw [heq]
    exact (canonical272 hH).trans (sound308 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1401 (1 : Fin 5)) =
      Sparse.eval value329 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1401 (1 : Fin 5) = raw469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1401 raw469; decide +kernel
    rw [heq]
    exact (canonical469 hH).trans (sound329 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1401 (2 : Fin 5)) =
      Sparse.eval value1138 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1401 (2 : Fin 5) = raw494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1401 raw494; decide +kernel
    rw [heq]
    exact (canonical494 hH).trans (sound1138 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1401 (3 : Fin 5)) =
      Sparse.eval value662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1401 (3 : Fin 5) = raw497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1401 raw497; decide +kernel
    rw [heq]
    exact (canonical497 hH).trans (sound662 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1401 (4 : Fin 5)) =
      Sparse.eval value338 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1401 (4 : Fin 5) = raw498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1401 raw498; decide +kernel
    rw [heq]
    exact (canonical498 hH).trans (sound338 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1401 + (injectiveMoment H (mergeFirst pivotMatrix1401 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1401 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1401 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1401 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1401 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1401, value1138, value308, value329, value338, value662, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1402 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem sound1402 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1402 = Sparse.eval value1402 (momentVector H) := by
  have heq : pivotMatrix1402 = (fun u v => node1402 (pivotPermutation1402 u) v) := by apply Matrix.ext; unfold pivotMatrix1402 node1402 pivotPermutation1402; decide +kernel
  have hmoment : injectiveMoment H node1402 = injectiveMoment H pivotMatrix1402 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1402 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1402 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1402 (0 : Fin 5)) =
      Sparse.eval value310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1402 (0 : Fin 5) = raw273 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1402 raw273; decide +kernel
    rw [heq]
    exact (canonical273 hH).trans (sound310 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1402 (1 : Fin 5)) =
      Sparse.eval value331 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1402 (1 : Fin 5) = raw473 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1402 raw473; decide +kernel
    rw [heq]
    exact (canonical473 hH).trans (sound331 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1402 (2 : Fin 5)) =
      Sparse.eval value662 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1402 (2 : Fin 5) = raw497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1402 raw497; decide +kernel
    rw [heq]
    exact (canonical497 hH).trans (sound662 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1402 (3 : Fin 5)) =
      Sparse.eval value339 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1402 (3 : Fin 5) = raw500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1402 raw500; decide +kernel
    rw [heq]
    exact (canonical500 hH).trans (sound339 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1402 (4 : Fin 5)) =
      Sparse.eval value340 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1402 (4 : Fin 5) = raw501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1402 raw501; decide +kernel
    rw [heq]
    exact (canonical501 hH).trans (sound340 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1402 + (injectiveMoment H (mergeFirst pivotMatrix1402 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1402 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1402 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1402 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1402 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1402, value310, value331, value339, value340, value662, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1403 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem sound1403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1403 = Sparse.eval value1403 (momentVector H) := by
  have heq : pivotMatrix1403 = (fun u v => node1403 (pivotPermutation1403 u) v) := by apply Matrix.ext; unfold pivotMatrix1403 node1403 pivotPermutation1403; decide +kernel
  have hmoment : injectiveMoment H node1403 = injectiveMoment H pivotMatrix1403 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1403 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1403 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1403 (0 : Fin 5)) =
      Sparse.eval value313 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1403 (0 : Fin 5) = raw281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1403 raw281; decide +kernel
    rw [heq]
    exact (canonical281 hH).trans (sound313 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1403 (1 : Fin 5)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1403 (1 : Fin 5) = raw507 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1403 raw507; decide +kernel
    rw [heq]
    exact (canonical507 hH).trans (sound222 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1403 (2 : Fin 5)) =
      Sparse.eval value222 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1403 (2 : Fin 5) = raw513 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1403 raw513; decide +kernel
    rw [heq]
    exact (canonical513 hH).trans (sound222 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1403 (3 : Fin 5)) =
      Sparse.eval value342 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1403 (3 : Fin 5) = raw516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1403 raw516; decide +kernel
    rw [heq]
    exact (canonical516 hH).trans (sound342 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1403 (4 : Fin 5)) =
      Sparse.eval value699 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1403 (4 : Fin 5) = raw517 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1403 raw517; decide +kernel
    rw [heq]
    exact (canonical517 hH).trans (sound699 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1403 + (injectiveMoment H (mergeFirst pivotMatrix1403 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1403 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1403 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1403 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1403 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1403, value222, value313, value342, value699, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1404 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1404 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem sound1404 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1404 = Sparse.eval value1404 (momentVector H) := by
  have heq : pivotMatrix1404 = (fun u v => node1404 (pivotPermutation1404 u) v) := by apply Matrix.ext; unfold pivotMatrix1404 node1404 pivotPermutation1404; decide +kernel
  have hmoment : injectiveMoment H node1404 = injectiveMoment H pivotMatrix1404 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1404 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1404 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1404 (0 : Fin 5)) =
      Sparse.eval value318 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1404 (0 : Fin 5) = raw290 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1404 raw290; decide +kernel
    rw [heq]
    exact (canonical290 hH).trans (sound318 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1404 (1 : Fin 5)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1404 (1 : Fin 5) = raw509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1404 raw509; decide +kernel
    rw [heq]
    exact (canonical509 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1404 (2 : Fin 5)) =
      Sparse.eval value348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1404 (2 : Fin 5) = raw528 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1404 raw528; decide +kernel
    rw [heq]
    exact (canonical528 hH).trans (sound348 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1404 (3 : Fin 5)) =
      Sparse.eval value349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1404 (3 : Fin 5) = raw530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1404 raw530; decide +kernel
    rw [heq]
    exact (canonical530 hH).trans (sound349 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1404 (4 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1404 (4 : Fin 5) = raw531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1404 raw531; decide +kernel
    rw [heq]
    exact (canonical531 hH).trans (sound697 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1404 + (injectiveMoment H (mergeFirst pivotMatrix1404 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1404 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1404 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1404 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1404 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1404, value170, value318, value348, value349, value697, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1405 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1405 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem sound1405 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1405 = Sparse.eval value1405 (momentVector H) := by
  have heq : pivotMatrix1405 = (fun u v => node1405 (pivotPermutation1405 u) v) := by apply Matrix.ext; unfold pivotMatrix1405 node1405 pivotPermutation1405; decide +kernel
  have hmoment : injectiveMoment H node1405 = injectiveMoment H pivotMatrix1405 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1405 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1405 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1405 (0 : Fin 5)) =
      Sparse.eval value320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (0 : Fin 5) = raw293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw293; decide +kernel
    rw [heq]
    exact (canonical293 hH).trans (sound320 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1405 (1 : Fin 5)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (1 : Fin 5) = raw511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw511; decide +kernel
    rw [heq]
    exact (canonical511 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1405 (2 : Fin 5)) =
      Sparse.eval value349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (2 : Fin 5) = raw530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw530; decide +kernel
    rw [heq]
    exact (canonical530 hH).trans (sound349 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1405 (3 : Fin 5)) =
      Sparse.eval value349 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (3 : Fin 5) = raw533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw533; decide +kernel
    rw [heq]
    exact (canonical533 hH).trans (sound349 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1405 (4 : Fin 5)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1405 (4 : Fin 5) = raw534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1405 raw534; decide +kernel
    rw [heq]
    exact (canonical534 hH).trans (sound1139 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1405 + (injectiveMoment H (mergeFirst pivotMatrix1405 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1405 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1405, value1139, value188, value320, value349, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1406 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1406 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem sound1406 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1406 = Sparse.eval value1406 (momentVector H) := by
  have heq : pivotMatrix1406 = (fun u v => node1406 (pivotPermutation1406 u) v) := by apply Matrix.ext; unfold pivotMatrix1406 node1406 pivotPermutation1406; decide +kernel
  have hmoment : injectiveMoment H node1406 = injectiveMoment H pivotMatrix1406 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1406 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1406 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1406 (0 : Fin 5)) =
      Sparse.eval value321 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1406 (0 : Fin 5) = raw303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1406 raw303; decide +kernel
    rw [heq]
    exact (canonical303 hH).trans (sound321 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1406 (1 : Fin 5)) =
      Sparse.eval value697 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1406 (1 : Fin 5) = raw531 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1406 raw531; decide +kernel
    rw [heq]
    exact (canonical531 hH).trans (sound697 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1406 (2 : Fin 5)) =
      Sparse.eval value350 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1406 (2 : Fin 5) = raw545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1406 raw545; decide +kernel
    rw [heq]
    exact (canonical545 hH).trans (sound350 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1406 (3 : Fin 5)) =
      Sparse.eval value351 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1406 (3 : Fin 5) = raw548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1406 raw548; decide +kernel
    rw [heq]
    exact (canonical548 hH).trans (sound351 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1406 (4 : Fin 5)) =
      Sparse.eval value651 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1406 (4 : Fin 5) = raw549 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1406 raw549; decide +kernel
    rw [heq]
    exact (canonical549 hH).trans (sound651 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1406 + (injectiveMoment H (mergeFirst pivotMatrix1406 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1406 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1406 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1406 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1406 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1406, value321, value350, value351, value651, value697, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation1407 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix1407 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem sound1407 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1407 = Sparse.eval value1407 (momentVector H) := by
  have heq : pivotMatrix1407 = (fun u v => node1407 (pivotPermutation1407 u) v) := by apply Matrix.ext; unfold pivotMatrix1407 node1407 pivotPermutation1407; decide +kernel
  have hmoment : injectiveMoment H node1407 = injectiveMoment H pivotMatrix1407 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1407 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1407 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1407 (0 : Fin 5)) =
      Sparse.eval value324 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1407 (0 : Fin 5) = raw315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1407 raw315; decide +kernel
    rw [heq]
    exact (canonical315 hH).trans (sound324 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1407 (1 : Fin 5)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1407 (1 : Fin 5) = raw551 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1407 raw551; decide +kernel
    rw [heq]
    exact (canonical551 hH).trans (sound663 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1407 (2 : Fin 5)) =
      Sparse.eval value339 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1407 (2 : Fin 5) = raw559 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1407 raw559; decide +kernel
    rw [heq]
    exact (canonical559 hH).trans (sound339 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1407 (3 : Fin 5)) =
      Sparse.eval value339 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1407 (3 : Fin 5) = raw561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1407 raw561; decide +kernel
    rw [heq]
    exact (canonical561 hH).trans (sound339 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1407 (4 : Fin 5)) =
      Sparse.eval value341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1407 (4 : Fin 5) = raw562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1407 raw562; decide +kernel
    rw [heq]
    exact (canonical562 hH).trans (sound341 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1407 + (injectiveMoment H (mergeFirst pivotMatrix1407 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1407 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1407 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1407 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1407 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1407, value324, value339, value341, value663, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
