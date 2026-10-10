import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical273
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical305
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical306
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical307

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal269 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def boundaryMatrix269 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def boundaryRow269 : Integer.Sparse (Fin 909) := [(0, 6), (1, -65), (2, -125), (3, -1360), (4, -160), (5, 420), (6, -70), (7, -320), (8, -160), (9, 60), (13, -960), (26, -640), (34, -400), (35, -1200), (52, -1040), (56, 480), (60, -400), (64, 240), (67, -160), (69, -240), (70, -160), (71, -160), (125, 480), (126, 240), (128, -320), (197, 240), (257, -160), (260, 240), (262, 480), (268, 480), (495, -240)]

theorem boundarySound269 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow269 (momentVector H) = 0 := by
  have hshape : boundaryMatrix269 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix269 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix269 (0 : Fin 6)) =
      Sparse.eval value1395 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix269 (0 : Fin 6) = raw8206 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8206 hH).trans (sound1395 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix269 (1 : Fin 6)) =
      Sparse.eval value563 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix269 (1 : Fin 6) = raw8683 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8683 hH).trans (sound563 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix269 (2 : Fin 6)) =
      Sparse.eval value1404 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix269 (2 : Fin 6) = raw8736 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8736 hH).trans (sound1404 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix269 (3 : Fin 6)) =
      Sparse.eval value1405 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix269 (3 : Fin 6) = raw8746 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8746 hH).trans (sound1405 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix269 (4 : Fin 6)) =
      Sparse.eval value1384 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix269 (4 : Fin 6) = raw8752 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8752 hH).trans (sound1384 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix269 (5 : Fin 6)) =
      Sparse.eval value2657 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix269 (5 : Fin 6) = raw8753 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8753 hH).trans (sound2657 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix269 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix269 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix269 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix269 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix269 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix269 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow269, value1384, value1395, value1404, value1405, value2657, value563, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal270 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def boundaryMatrix270 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def boundaryRow270 : Integer.Sparse (Fin 909) := [(0, 9), (1, -45), (2, -85), (3, -800), (4, -80), (5, 460), (6, -85), (7, -640), (8, -480), (9, 100), (26, -400), (35, -560), (51, 240), (52, -400), (69, -320), (70, -80), (71, -480), (123, 480), (124, 480), (126, 240), (197, 240), (236, 480), (259, 240), (495, -80)]

theorem boundarySound270 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow270 (momentVector H) = 0 := by
  have hshape : boundaryMatrix270 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix270 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix270 (0 : Fin 6)) =
      Sparse.eval value1849 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix270 (0 : Fin 6) = raw6846 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6846 hH).trans (sound1849 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix270 (1 : Fin 6)) =
      Sparse.eval value1858 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix270 (1 : Fin 6) = raw8538 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8538 hH).trans (sound1858 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix270 (2 : Fin 6)) =
      Sparse.eval value1858 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix270 (2 : Fin 6) = raw8693 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8693 hH).trans (sound1858 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix270 (3 : Fin 6)) =
      Sparse.eval value1873 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix270 (3 : Fin 6) = raw8712 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8712 hH).trans (sound1873 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix270 (4 : Fin 6)) =
      Sparse.eval value1383 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix270 (4 : Fin 6) = raw8719 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8719 hH).trans (sound1383 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix270 (5 : Fin 6)) =
      Sparse.eval value1883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix270 (5 : Fin 6) = raw8722 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8722 hH).trans (sound1883 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix270 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix270 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix270 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix270 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix270 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix270 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow270, value1383, value1849, value1858, value1873, value1883, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal271 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def boundaryMatrix271 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def boundaryRow271 : Integer.Sparse (Fin 909) := [(0, 1), (1, -3), (2, -12), (3, -112), (5, 16), (6, -2), (12, -32), (13, -144), (26, -16), (33, 48), (34, -32), (35, -32), (52, -96), (55, 96), (59, 96), (60, -16), (61, 48), (64, 96), (69, -32), (71, -16), (125, 96), (128, -32), (197, 48), (256, 48), (260, 48), (263, -96), (495, -16)]

theorem boundarySound271 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow271 (momentVector H) = 0 := by
  have hshape : boundaryMatrix271 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix271 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix271 (0 : Fin 6)) =
      Sparse.eval value1401 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix271 (0 : Fin 6) = raw8193 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8193 hH).trans (sound1401 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix271 (1 : Fin 6)) =
      Sparse.eval value1138 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix271 (1 : Fin 6) = raw8674 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8674 hH).trans (sound1138 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix271 (2 : Fin 6)) =
      Sparse.eval value1138 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix271 (2 : Fin 6) = raw8698 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8698 hH).trans (sound1138 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix271 (3 : Fin 6)) =
      Sparse.eval value2654 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix271 (3 : Fin 6) = raw8708 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8708 hH).trans (sound2654 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix271 (4 : Fin 6)) =
      Sparse.eval value1400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix271 (4 : Fin 6) = raw8709 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8709 hH).trans (sound1400 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix271 (5 : Fin 6)) =
      Sparse.eval value1423 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix271 (5 : Fin 6) = raw8710 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8710 hH).trans (sound1423 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix271 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix271 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix271 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix271 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix271 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix271 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow271, value1138, value1400, value1401, value1423, value2654, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal273 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def boundaryMatrix273 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def boundaryRow273 : Integer.Sparse (Fin 909) := [(0, 7), (1, 95), (2, -25), (3, -1920), (4, -560), (5, 180), (6, -15), (7, -720), (8, -160), (12, -160), (13, -80), (23, 240), (25, 480), (26, -1120), (33, 240), (34, -240), (35, -960), (51, 240), (52, -240), (54, 240), (55, 240), (64, 480), (67, -320), (69, -80), (70, -80), (81, 480), (123, 480), (124, 240), (125, 240), (256, 240), (257, -80), (259, 240), (266, 240), (487, -480), (495, -80)]

theorem boundarySound273 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow273 (momentVector H) = 0 := by
  have hshape : boundaryMatrix273 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix273 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix273 (0 : Fin 6)) =
      Sparse.eval value1864 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix273 (0 : Fin 6) = raw8213 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8213 hH).trans (sound1864 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix273 (1 : Fin 6)) =
      Sparse.eval value702 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix273 (1 : Fin 6) = raw8690 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8690 hH).trans (sound702 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix273 (2 : Fin 6)) =
      Sparse.eval value1865 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix273 (2 : Fin 6) = raw8743 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8743 hH).trans (sound1865 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix273 (3 : Fin 6)) =
      Sparse.eval value2463 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix273 (3 : Fin 6) = raw8767 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8767 hH).trans (sound2463 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix273 (4 : Fin 6)) =
      Sparse.eval value1866 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix273 (4 : Fin 6) = raw8768 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8768 hH).trans (sound1866 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix273 (5 : Fin 6)) =
      Sparse.eval value1527 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix273 (5 : Fin 6) = raw8769 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8769 hH).trans (sound1527 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix273 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix273 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix273 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix273 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix273 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix273 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow273, value1527, value1864, value1865, value1866, value2463, value702, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal275 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def boundaryMatrix275 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def boundaryRow275 : Integer.Sparse (Fin 909) := [(0, 8), (1, 35), (2, -340), (3, -3120), (4, -800), (5, 680), (6, -55), (7, -1920), (8, -800), (10, 240), (11, -160), (12, -80), (13, -160), (26, -1760), (33, 480), (34, -320), (35, -2640), (52, -800), (55, 240), (67, -800), (81, 1920), (82, -80), (228, 480), (273, 480), (276, -160), (306, 480), (307, 480)]

theorem boundarySound275 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow275 (momentVector H) = 0 := by
  have hshape : boundaryMatrix275 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix275 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix275 (0 : Fin 6)) =
      Sparse.eval value1534 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix275 (0 : Fin 6) = raw8220 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8220 hH).trans (sound1534 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix275 (1 : Fin 6)) =
      Sparse.eval value1533 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix275 (1 : Fin 6) = raw8783 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8783 hH).trans (sound1533 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix275 (2 : Fin 6)) =
      Sparse.eval value1530 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix275 (2 : Fin 6) = raw8789 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8789 hH).trans (sound1530 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix275 (3 : Fin 6)) =
      Sparse.eval value1530 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix275 (3 : Fin 6) = raw8791 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8791 hH).trans (sound1530 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix275 (4 : Fin 6)) =
      Sparse.eval value1535 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix275 (4 : Fin 6) = raw8794 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8794 hH).trans (sound1535 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix275 (5 : Fin 6)) =
      Sparse.eval value1434 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix275 (5 : Fin 6) = raw8795 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8795 hH).trans (sound1434 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix275 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix275 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix275 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix275 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix275 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix275 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow275, value1434, value1530, value1533, value1534, value1535, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal276 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def boundaryMatrix276 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def boundaryRow276 : Integer.Sparse (Fin 909) := [(0, 1), (1, -12), (2, -27), (3, -224), (4, -16), (5, 52), (6, -8), (7, -16), (8, -16), (11, -16), (12, -88), (13, -304), (26, -32), (33, 96), (34, -32), (35, -144), (52, -176), (54, 48), (59, 240), (60, -64), (82, -32), (128, -96), (199, 24), (201, 48), (228, 48), (271, 48), (276, -16), (490, 96), (721, 96)]

theorem boundarySound276 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow276 (momentVector H) = 0 := by
  have hshape : boundaryMatrix276 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix276 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix276 (0 : Fin 6)) =
      Sparse.eval value2107 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix276 (0 : Fin 6) = raw8218 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8218 hH).trans (sound2107 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix276 (1 : Fin 6)) =
      Sparse.eval value2108 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix276 (1 : Fin 6) = raw8781 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8781 hH).trans (sound2108 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix276 (2 : Fin 6)) =
      Sparse.eval value2108 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix276 (2 : Fin 6) = raw8784 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8784 hH).trans (sound2108 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix276 (3 : Fin 6)) =
      Sparse.eval value1388 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix276 (3 : Fin 6) = raw8785 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8785 hH).trans (sound1388 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix276 (4 : Fin 6)) =
      Sparse.eval value1869 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix276 (4 : Fin 6) = raw8786 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8786 hH).trans (sound1869 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix276 (5 : Fin 6)) =
      Sparse.eval value1432 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix276 (5 : Fin 6) = raw8787 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8787 hH).trans (sound1432 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix276 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix276 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix276 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix276 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix276 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix276 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow276, value1388, value1432, value1869, value2107, value2108, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal277 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def boundaryMatrix277 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def boundaryRow277 : Integer.Sparse (Fin 909) := [(0, 6), (1, 65), (2, -180), (3, -2880), (4, -720), (5, 440), (6, -35), (7, -1680), (8, -480), (11, -240), (13, -240), (26, -1920), (34, -480), (35, -2800), (52, -720), (60, -160), (67, -960), (81, 1440), (228, 720), (273, 720), (276, -240)]

theorem boundarySound277 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow277 (momentVector H) = 0 := by
  have hshape : boundaryMatrix277 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix277 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix277 (0 : Fin 6)) =
      Sparse.eval value1532 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix277 (0 : Fin 6) = raw6803 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6803 hH).trans (sound1532 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix277 (1 : Fin 6)) =
      Sparse.eval value1532 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix277 (1 : Fin 6) = raw8525 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8525 hH).trans (sound1532 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix277 (2 : Fin 6)) =
      Sparse.eval value1532 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix277 (2 : Fin 6) = raw8572 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8572 hH).trans (sound1532 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix277 (3 : Fin 6)) =
      Sparse.eval value437 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix277 (3 : Fin 6) = raw8588 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8588 hH).trans (sound437 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix277 (4 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix277 (4 : Fin 6) = raw8600 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8600 hH).trans (sound1542 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix277 (5 : Fin 6)) =
      Sparse.eval value1387 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix277 (5 : Fin 6) = raw8602 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8602 hH).trans (sound1387 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix277 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix277 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix277 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix277 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix277 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix277 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow277, value1387, value1532, value1542, value437, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal278 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def boundaryMatrix278 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def boundaryRow278 : Integer.Sparse (Fin 909) := [(0, 1), (1, 6), (2, -39), (3, -576), (4, -160), (5, 108), (6, -14), (7, -192), (8, -64), (11, -128), (12, -32), (13, -112), (26, -352), (33, 96), (34, -64), (35, -544), (52, -256), (54, 48), (56, 96), (59, 96), (60, -64), (67, -64), (81, 192), (128, -16), (228, 480), (271, 48), (275, 96), (276, -48), (490, 192), (721, 96)]

theorem boundarySound278 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow278 (momentVector H) = 0 := by
  have hshape : boundaryMatrix278 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix278 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix278 (0 : Fin 6)) =
      Sparse.eval value2294 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix278 (0 : Fin 6) = raw6825 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6825 hH).trans (sound2294 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix278 (1 : Fin 6)) =
      Sparse.eval value2294 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix278 (1 : Fin 6) = raw8533 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8533 hH).trans (sound2294 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix278 (2 : Fin 6)) =
      Sparse.eval value2302 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix278 (2 : Fin 6) = raw8594 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8594 hH).trans (sound2302 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix278 (3 : Fin 6)) =
      Sparse.eval value2302 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix278 (3 : Fin 6) = raw8649 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8649 hH).trans (sound2302 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix278 (4 : Fin 6)) =
      Sparse.eval value1424 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix278 (4 : Fin 6) = raw8651 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8651 hH).trans (sound1424 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix278 (5 : Fin 6)) =
      Sparse.eval value2297 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix278 (5 : Fin 6) = raw8653 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8653 hH).trans (sound2297 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix278 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix278 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix278 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix278 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix278 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix278 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow278, value1424, value2294, value2297, value2302, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal285 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def boundaryMatrix285 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def boundaryRow285 : Integer.Sparse (Fin 909) := [(0, 7), (1, 105), (2, -120), (3, -1920), (4, -240), (12, -960), (13, -2000), (26, -240), (32, -80), (33, 1440), (34, -480), (51, 720), (52, -240), (60, -240), (61, 720), (127, 720), (128, -240), (489, 1440)]

theorem boundarySound285 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow285 (momentVector H) = 0 := by
  have hshape : boundaryMatrix285 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix285 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix285 (0 : Fin 6)) =
      Sparse.eval value1862 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix285 (0 : Fin 6) = raw6800 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6800 hH).trans (sound1862 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix285 (1 : Fin 6)) =
      Sparse.eval value1862 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix285 (1 : Fin 6) = raw8522 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8522 hH).trans (sound1862 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix285 (2 : Fin 6)) =
      Sparse.eval value1862 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix285 (2 : Fin 6) = raw8569 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8569 hH).trans (sound1862 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix285 (3 : Fin 6)) =
      Sparse.eval value1888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix285 (3 : Fin 6) = raw8583 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8583 hH).trans (sound1888 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix285 (4 : Fin 6)) =
      Sparse.eval value1411 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix285 (4 : Fin 6) = raw8593 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8593 hH).trans (sound1411 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix285 (5 : Fin 6)) =
      Sparse.eval value1890 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix285 (5 : Fin 6) = raw8595 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8595 hH).trans (sound1890 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix285 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix285 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix285 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix285 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix285 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix285 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow285, value1411, value1862, value1888, value1890, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal286 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def boundaryMatrix286 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def boundaryRow286 : Integer.Sparse (Fin 909) := [(0, 14), (1, -65), (2, -80), (3, -1200), (5, 340), (6, -65), (12, -160), (13, -1280), (26, -240), (33, 240), (34, -160), (35, -560), (52, -1120), (60, -160), (82, -80), (123, 480), (128, -320), (237, 480), (306, 240), (489, 480)]

theorem boundarySound286 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow286 (momentVector H) = 0 := by
  have hshape : boundaryMatrix286 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix286 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix286 (0 : Fin 6)) =
      Sparse.eval value1867 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (0 : Fin 6) = raw6859 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6859 hH).trans (sound1867 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix286 (1 : Fin 6)) =
      Sparse.eval value1854 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (1 : Fin 6) = raw8543 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8543 hH).trans (sound1854 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix286 (2 : Fin 6)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (2 : Fin 6) = raw8703 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8703 hH).trans (sound559 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix286 (3 : Fin 6)) =
      Sparse.eval value559 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (3 : Fin 6) = raw8770 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8770 hH).trans (sound559 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix286 (4 : Fin 6)) =
      Sparse.eval value1405 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (4 : Fin 6) = raw8773 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8773 hH).trans (sound1405 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix286 (5 : Fin 6)) =
      Sparse.eval value1887 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix286 (5 : Fin 6) = raw8774 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8774 hH).trans (sound1887 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix286 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix286 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow286, value1405, value1854, value1867, value1887, value559, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal287 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def boundaryMatrix287 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def boundaryRow287 : Integer.Sparse (Fin 909) := [(0, 7), (1, -10), (2, -25), (3, -480), (5, 200), (6, -30), (11, -40), (12, -40), (13, -480), (26, -200), (33, 120), (35, -440), (52, -440), (55, 120), (63, 240), (82, -40), (123, 240), (128, -40), (237, 240), (306, 120), (721, 120)]

theorem boundarySound287 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow287 (momentVector H) = 0 := by
  have hshape : boundaryMatrix287 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix287 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix287 (0 : Fin 6)) =
      Sparse.eval value2106 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix287 (0 : Fin 6) = raw4132 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4132 hH).trans (sound2106 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix287 (1 : Fin 6)) =
      Sparse.eval value1858 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix287 (1 : Fin 6) = raw7398 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7398 hH).trans (sound1858 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix287 (2 : Fin 6)) =
      Sparse.eval value2465 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix287 (2 : Fin 6) = raw7447 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7447 hH).trans (sound2465 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix287 (3 : Fin 6)) =
      Sparse.eval value862 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix287 (3 : Fin 6) = raw7454 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7454 hH).trans (sound862 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix287 (4 : Fin 6)) =
      Sparse.eval value1861 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix287 (4 : Fin 6) = raw7455 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7455 hH).trans (sound1861 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix287 (5 : Fin 6)) =
      Sparse.eval value2468 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix287 (5 : Fin 6) = raw7456 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7456 hH).trans (sound2468 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix287 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix287 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix287 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix287 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix287 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix287 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow287, value1858, value1861, value2106, value2465, value2468, value862, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal297 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def boundaryMatrix297 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def boundaryRow297 : Integer.Sparse (Fin 909) := [(0, -5), (1, 131), (2, 228), (3, 224), (5, -556), (6, 42), (7, 656), (8, 928), (9, -120), (35, 224), (52, 192), (69, 848), (70, 272), (71, 1664), (256, -576), (277, -144), (279, 144), (280, 576), (281, 576), (726, -144), (818, -288)]

theorem boundarySound297 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow297 (momentVector H) = 0 := by
  have hshape : boundaryMatrix297 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix297 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix297 (0 : Fin 6)) =
      Sparse.eval value2868 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix297 (0 : Fin 6) = raw3371 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3371 hH).trans (sound2868 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix297 (1 : Fin 6)) =
      Sparse.eval value2867 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix297 (1 : Fin 6) = raw7264 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7264 hH).trans (sound2867 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix297 (2 : Fin 6)) =
      Sparse.eval value2866 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix297 (2 : Fin 6) = raw7294 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7294 hH).trans (sound2866 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix297 (3 : Fin 6)) =
      Sparse.eval value2866 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix297 (3 : Fin 6) = raw7311 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7311 hH).trans (sound2866 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix297 (4 : Fin 6)) =
      Sparse.eval value3330 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix297 (4 : Fin 6) = raw7314 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7314 hH).trans (sound3330 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix297 (5 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix297 (5 : Fin 6) = raw7315 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7315 hH).trans (sound3439 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix297 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix297 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix297 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix297 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix297 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix297 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow297, value2866, value2867, value2868, value3330, value3439, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal298 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def boundaryMatrix298 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def boundaryRow298 : Integer.Sparse (Fin 909) := [(0, -23), (1, -195), (2, 220), (3, 3200), (5, -420), (6, 30), (7, 1520), (8, 640), (9, -40), (10, -240), (12, 560), (13, 160), (23, -1920), (24, -960), (26, 320), (27, 420), (35, 800), (51, -1440), (54, -1680), (55, -1440), (69, 400), (70, 240), (71, 160), (77, 2880), (79, 720), (228, -960), (277, -240), (290, 1440), (291, 2160)]

theorem boundarySound298 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow298 (momentVector H) = 0 := by
  have hshape : boundaryMatrix298 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix298 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix298 (0 : Fin 6)) =
      Sparse.eval value2882 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix298 (0 : Fin 6) = raw9133 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9133 hH).trans (sound2882 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix298 (1 : Fin 6)) =
      Sparse.eval value2786 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix298 (1 : Fin 6) = raw9401 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9401 hH).trans (sound2786 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix298 (2 : Fin 6)) =
      Sparse.eval value2884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix298 (2 : Fin 6) = raw9463 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9463 hH).trans (sound2884 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix298 (3 : Fin 6)) =
      Sparse.eval value2884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix298 (3 : Fin 6) = raw9484 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9484 hH).trans (sound2884 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix298 (4 : Fin 6)) =
      Sparse.eval value2885 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix298 (4 : Fin 6) = raw9495 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9495 hH).trans (sound2885 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix298 (5 : Fin 6)) =
      Sparse.eval value3421 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix298 (5 : Fin 6) = raw9496 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9496 hH).trans (sound3421 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix298 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix298 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix298 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix298 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix298 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix298 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow298, value2786, value2882, value2884, value2885, value3421, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal300 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def boundaryMatrix300 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def boundaryRow300 : Integer.Sparse (Fin 909) := [(0, -19), (1, -115), (2, 430), (3, 3200), (5, -740), (6, 20), (7, 2800), (8, 1280), (9, -40), (10, -720), (12, 720), (13, 960), (23, -240), (24, -480), (27, 180), (35, 2240), (51, -1920), (52, 640), (54, -960), (59, -1920), (69, 720), (70, 400), (71, 320), (72, 720), (73, 1440), (74, 1440), (199, -720), (256, -960), (277, -240), (279, 720), (280, 1440), (726, -720)]

theorem boundarySound300 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow300 (momentVector H) = 0 := by
  have hshape : boundaryMatrix300 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix300 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix300 (0 : Fin 6)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix300 (0 : Fin 6) = raw9710 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9710 hH).trans (sound2749 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix300 (1 : Fin 6)) =
      Sparse.eval value2749 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix300 (1 : Fin 6) = raw9774 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9774 hH).trans (sound2749 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix300 (2 : Fin 6)) =
      Sparse.eval value2873 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix300 (2 : Fin 6) = raw9816 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9816 hH).trans (sound2873 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix300 (3 : Fin 6)) =
      Sparse.eval value2873 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix300 (3 : Fin 6) = raw9829 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9829 hH).trans (sound2873 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix300 (4 : Fin 6)) =
      Sparse.eval value2876 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix300 (4 : Fin 6) = raw9837 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9837 hH).trans (sound2876 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix300 (5 : Fin 6)) =
      Sparse.eval value2865 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix300 (5 : Fin 6) = raw9838 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9838 hH).trans (sound2865 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix300 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix300 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix300 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix300 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix300 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix300 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow300, value2749, value2865, value2873, value2876, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal301 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def boundaryMatrix301 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def boundaryRow301 : Integer.Sparse (Fin 909) := [(0, -3), (1, 41), (2, 126), (3, 176), (4, 48), (5, -208), (6, 16), (7, 304), (8, 352), (9, -32), (10, -96), (12, 32), (13, 16), (24, -96), (26, 32), (27, 24), (30, -48), (35, 80), (51, -144), (52, 48), (54, -48), (55, -48), (56, -192), (59, -96), (69, 144), (70, 16), (71, 480), (74, 288), (75, 144), (78, 288), (201, -96), (228, -96), (256, -96), (277, -48), (280, 144), (282, 144), (288, 288), (289, 288), (726, -48), (818, -48)]

theorem boundarySound301 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow301 (momentVector H) = 0 := by
  have hshape : boundaryMatrix301 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix301 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix301 (0 : Fin 6)) =
      Sparse.eval value2747 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix301 (0 : Fin 6) = raw9713 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9713 hH).trans (sound2747 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix301 (1 : Fin 6)) =
      Sparse.eval value2747 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix301 (1 : Fin 6) = raw9777 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9777 hH).trans (sound2747 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix301 (2 : Fin 6)) =
      Sparse.eval value2874 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix301 (2 : Fin 6) = raw9824 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9824 hH).trans (sound2874 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix301 (3 : Fin 6)) =
      Sparse.eval value2871 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix301 (3 : Fin 6) = raw9845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9845 hH).trans (sound2871 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix301 (4 : Fin 6)) =
      Sparse.eval value2875 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix301 (4 : Fin 6) = raw9846 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9846 hH).trans (sound2875 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix301 (5 : Fin 6)) =
      Sparse.eval value2864 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix301 (5 : Fin 6) = raw9847 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9847 hH).trans (sound2864 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix301 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix301 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix301 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix301 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix301 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix301 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow301, value2747, value2864, value2871, value2874, value2875, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal302 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def boundaryMatrix302 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

def boundaryRow302 : Integer.Sparse (Fin 909) := [(0, -5), (1, 101), (2, 210), (3, 336), (4, 16), (5, -360), (6, 26), (7, 352), (8, 576), (9, -24), (35, 144), (51, -144), (52, 288), (69, 208), (70, 80), (71, 320), (81, -192), (86, 288), (256, -96), (281, 288), (322, 144), (325, 288), (327, 288), (818, -144)]

theorem boundarySound302 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow302 (momentVector H) = 0 := by
  have hshape : boundaryMatrix302 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix302 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix302 (0 : Fin 6)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (0 : Fin 6) = raw9712 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9712 hH).trans (sound2400 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix302 (1 : Fin 6)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (1 : Fin 6) = raw9776 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9776 hH).trans (sound2400 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix302 (2 : Fin 6)) =
      Sparse.eval value2920 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (2 : Fin 6) = raw9823 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9823 hH).trans (sound2920 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix302 (3 : Fin 6)) =
      Sparse.eval value2927 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (3 : Fin 6) = raw9840 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9840 hH).trans (sound2927 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix302 (4 : Fin 6)) =
      Sparse.eval value2928 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (4 : Fin 6) = raw9843 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9843 hH).trans (sound2928 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix302 (5 : Fin 6)) =
      Sparse.eval value2867 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (5 : Fin 6) = raw9844 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9844 hH).trans (sound2867 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix302 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow302, value2400, value2867, value2920, value2927, value2928, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
