import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical273
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical286
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical293
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical295
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical296
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical299
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical300
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical301
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical302
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical303
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical304
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical310
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical312
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical313

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal68 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def boundaryMatrix68 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def boundaryRow68 : Integer.Sparse (Fin 909) := [(0, 8), (1, 40), (2, -15), (3, -1120), (5, 60), (6, -15), (7, -160), (12, -320), (13, -800), (23, 240), (26, -480), (33, 480), (34, -320), (35, -480), (54, 480), (55, 480), (63, 240), (65, 480), (67, -160)]

theorem boundarySound68 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow68 (momentVector H) = 0 := by
  have hshape : boundaryMatrix68 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix68 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix68 (0 : Fin 6)) =
      Sparse.eval value1417 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix68 (0 : Fin 6) = raw8200 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8200 hH).trans (sound1417 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix68 (1 : Fin 6)) =
      Sparse.eval value869 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix68 (1 : Fin 6) = raw8678 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8678 hH).trans (sound869 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix68 (2 : Fin 6)) =
      Sparse.eval value869 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix68 (2 : Fin 6) = raw8702 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8702 hH).trans (sound869 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix68 (3 : Fin 6)) =
      Sparse.eval value1426 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix68 (3 : Fin 6) = raw8718 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8718 hH).trans (sound1426 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix68 (4 : Fin 6)) =
      Sparse.eval value1427 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix68 (4 : Fin 6) = raw8727 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8727 hH).trans (sound1427 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix68 (5 : Fin 6)) =
      Sparse.eval value2788 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix68 (5 : Fin 6) = raw8728 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8728 hH).trans (sound2788 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix68 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix68 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix68 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix68 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix68 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix68 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow68, value1417, value1426, value1427, value2788, value869, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal69 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def boundaryMatrix69 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def boundaryRow69 : Integer.Sparse (Fin 909) := [(0, -2), (1, 67), (2, -13), (3, -528), (4, -224), (5, 16), (6, -2), (7, -16), (8, -16), (12, -16), (13, -80), (24, 48), (26, -336), (33, 48), (34, -112), (35, -64), (52, -16), (55, 144), (56, 96), (64, 48), (66, 96), (67, -32)]

theorem boundarySound69 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow69 (momentVector H) = 0 := by
  have hshape : boundaryMatrix69 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix69 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix69 (0 : Fin 6)) =
      Sparse.eval value1419 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix69 (0 : Fin 6) = raw8210 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8210 hH).trans (sound1419 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix69 (1 : Fin 6)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix69 (1 : Fin 6) = raw8687 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8687 hH).trans (sound872 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix69 (2 : Fin 6)) =
      Sparse.eval value1429 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix69 (2 : Fin 6) = raw8740 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8740 hH).trans (sound1429 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix69 (3 : Fin 6)) =
      Sparse.eval value1430 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix69 (3 : Fin 6) = raw8751 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8751 hH).trans (sound1430 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix69 (4 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix69 (4 : Fin 6) = raw8759 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8759 hH).trans (sound2469 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix69 (5 : Fin 6)) =
      Sparse.eval value2657 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix69 (5 : Fin 6) = raw8760 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8760 hH).trans (sound2657 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix69 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix69 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix69 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix69 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix69 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix69 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow69, value1419, value1429, value1430, value2469, value2657, value872, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal70 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def boundaryMatrix70 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def boundaryRow70 : Integer.Sparse (Fin 909) := [(0, 9), (1, -5), (2, -65), (3, -1440), (5, 60), (6, -5), (12, -720), (13, -2640), (26, -240), (32, -320), (34, -480), (35, -240), (52, -480), (59, 720), (60, -400), (61, 720), (128, -240)]

theorem boundarySound70 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow70 (momentVector H) = 0 := by
  have hshape : boundaryMatrix70 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix70 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix70 (0 : Fin 6)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix70 (0 : Fin 6) = raw9696 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9696 hH).trans (sound663 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix70 (1 : Fin 6)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix70 (1 : Fin 6) = raw10006 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10006 hH).trans (sound663 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix70 (2 : Fin 6)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix70 (2 : Fin 6) = raw10014 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10014 hH).trans (sound663 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix70 (3 : Fin 6)) =
      Sparse.eval value1410 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix70 (3 : Fin 6) = raw10024 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10024 hH).trans (sound1410 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix70 (4 : Fin 6)) =
      Sparse.eval value1411 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix70 (4 : Fin 6) = raw10029 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10029 hH).trans (sound1411 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix70 (5 : Fin 6)) =
      Sparse.eval value1388 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix70 (5 : Fin 6) = raw10030 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10030 hH).trans (sound1388 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix70 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix70 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix70 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix70 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix70 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix70 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow70, value1388, value1410, value1411, value663, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal71 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def boundaryMatrix71 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def boundaryRow71 : Integer.Sparse (Fin 909) := [(0, 1), (2, -7), (3, -144), (5, 14), (6, -2), (7, -24), (12, -48), (13, -160), (26, -24), (32, -16), (33, 72), (35, -72), (52, -48), (54, 72), (60, -16), (62, 48)]

theorem boundarySound71 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow71 (momentVector H) = 0 := by
  have hshape : boundaryMatrix71 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix71 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix71 (0 : Fin 6)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix71 (0 : Fin 6) = raw9693 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9693 hH).trans (sound1139 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix71 (1 : Fin 6)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix71 (1 : Fin 6) = raw10003 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10003 hH).trans (sound1139 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix71 (2 : Fin 6)) =
      Sparse.eval value1139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix71 (2 : Fin 6) = raw10011 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10011 hH).trans (sound1139 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix71 (3 : Fin 6)) =
      Sparse.eval value1409 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix71 (3 : Fin 6) = raw10018 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10018 hH).trans (sound1409 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix71 (4 : Fin 6)) =
      Sparse.eval value1410 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix71 (4 : Fin 6) = raw10024 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10024 hH).trans (sound1410 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix71 (5 : Fin 6)) =
      Sparse.eval value1387 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix71 (5 : Fin 6) = raw10025 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10025 hH).trans (sound1387 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix71 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix71 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix71 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix71 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix71 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix71 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow71, value1139, value1387, value1409, value1410, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal72 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def boundaryMatrix72 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def boundaryRow72 : Integer.Sparse (Fin 909) := [(0, -16), (1, 485), (2, -240), (3, -3440), (4, -1280), (5, 120), (6, -5), (7, -480), (8, -160), (12, -320), (13, -320), (25, 240), (26, -1600), (31, 480), (33, 960), (34, -400), (35, -560), (51, 480), (52, -240), (64, 240), (67, -160), (81, 480), (123, 480)]

theorem boundarySound72 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow72 (momentVector H) = 0 := by
  have hshape : boundaryMatrix72 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix72 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix72 (0 : Fin 6)) =
      Sparse.eval value708 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix72 (0 : Fin 6) = raw9698 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9698 hH).trans (sound708 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix72 (1 : Fin 6)) =
      Sparse.eval value1868 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix72 (1 : Fin 6) = raw10035 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10035 hH).trans (sound1868 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix72 (2 : Fin 6)) =
      Sparse.eval value1434 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix72 (2 : Fin 6) = raw10036 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10036 hH).trans (sound1434 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix72 (3 : Fin 6)) =
      Sparse.eval value1434 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix72 (3 : Fin 6) = raw10037 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10037 hH).trans (sound1434 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix72 (4 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix72 (4 : Fin 6) = raw10038 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10038 hH).trans (sound2469 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix72 (5 : Fin 6)) =
      Sparse.eval value1530 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix72 (5 : Fin 6) = raw10039 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10039 hH).trans (sound1530 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix72 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix72 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix72 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix72 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix72 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix72 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow72, value1434, value1530, value1868, value2469, value708, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal73 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def boundaryMatrix73 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def boundaryRow73 : Integer.Sparse (Fin 909) := [(1, 42), (2, -35), (3, -448), (4, -64), (5, 44), (6, -5), (7, -112), (8, -32), (12, -128), (13, -272), (26, -160), (34, -80), (35, -160), (51, 96), (52, -112), (54, 48), (64, 48), (67, -32)]

theorem boundarySound73 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow73 (momentVector H) = 0 := by
  have hshape : boundaryMatrix73 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix73 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix73 (0 : Fin 6)) =
      Sparse.eval value1859 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix73 (0 : Fin 6) = raw3952 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3952 hH).trans (sound1859 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix73 (1 : Fin 6)) =
      Sparse.eval value1860 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix73 (1 : Fin 6) = raw7362 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7362 hH).trans (sound1860 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix73 (2 : Fin 6)) =
      Sparse.eval value1428 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix73 (2 : Fin 6) = raw7388 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7388 hH).trans (sound1428 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix73 (3 : Fin 6)) =
      Sparse.eval value1885 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix73 (3 : Fin 6) = raw7393 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7393 hH).trans (sound1885 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix73 (4 : Fin 6)) =
      Sparse.eval value1861 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix73 (4 : Fin 6) = raw7394 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7394 hH).trans (sound1861 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix73 (5 : Fin 6)) =
      Sparse.eval value2666 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix73 (5 : Fin 6) = raw7395 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7395 hH).trans (sound2666 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix73 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix73 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix73 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix73 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix73 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix73 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow73, value1428, value1859, value1860, value1861, value1885, value2666, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal74 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def boundaryMatrix74 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def boundaryRow74 : Integer.Sparse (Fin 909) := [(0, -9), (1, 345), (2, -120), (3, -2560), (4, -880), (7, -80), (12, -800), (13, -480), (23, 240), (25, 720), (26, -880), (31, 480), (33, 1440), (34, -320), (35, -160), (54, 480), (65, 240), (67, -80), (81, 240), (195, -480)]

theorem boundarySound74 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow74 (momentVector H) = 0 := by
  have hshape : boundaryMatrix74 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix74 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix74 (0 : Fin 6)) =
      Sparse.eval value2101 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (0 : Fin 6) = raw8211 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8211 hH).trans (sound2101 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix74 (1 : Fin 6)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (1 : Fin 6) = raw8688 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8688 hH).trans (sound705 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix74 (2 : Fin 6)) =
      Sparse.eval value2100 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (2 : Fin 6) = raw8741 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8741 hH).trans (sound2100 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix74 (3 : Fin 6)) =
      Sparse.eval value1866 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (3 : Fin 6) = raw8761 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8761 hH).trans (sound1866 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix74 (4 : Fin 6)) =
      Sparse.eval value2666 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (4 : Fin 6) = raw8762 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8762 hH).trans (sound2666 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix74 (5 : Fin 6)) =
      Sparse.eval value2097 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (5 : Fin 6) = raw8763 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8763 hH).trans (sound2097 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix74 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow74, value1866, value2097, value2100, value2101, value2666, value705, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal75 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def boundaryMatrix75 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def boundaryRow75 : Integer.Sparse (Fin 909) := [(0, 1), (1, 65), (2, -40), (3, -620), (4, -140), (5, 5), (12, -260), (13, -340), (25, 60), (26, -100), (27, -15), (31, 120), (33, 360), (34, -80), (35, -20), (51, 180), (52, -60), (55, 60), (59, 120), (60, -20), (61, 60), (128, -20), (194, -120)]

theorem boundarySound75 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow75 (momentVector H) = 0 := by
  have hshape : boundaryMatrix75 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix75 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix75 (0 : Fin 6)) =
      Sparse.eval value2091 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix75 (0 : Fin 6) = raw8212 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8212 hH).trans (sound2091 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix75 (1 : Fin 6)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix75 (1 : Fin 6) = raw8689 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8689 hH).trans (sound670 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix75 (2 : Fin 6)) =
      Sparse.eval value2097 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix75 (2 : Fin 6) = raw8742 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8742 hH).trans (sound2097 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix75 (3 : Fin 6)) =
      Sparse.eval value2661 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix75 (3 : Fin 6) = raw8764 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8764 hH).trans (sound2661 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix75 (4 : Fin 6)) =
      Sparse.eval value1853 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix75 (4 : Fin 6) = raw8765 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8765 hH).trans (sound1853 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix75 (5 : Fin 6)) =
      Sparse.eval value2100 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix75 (5 : Fin 6) = raw8766 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8766 hH).trans (sound2100 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix75 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix75 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix75 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix75 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix75 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix75 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow75, value1853, value2091, value2097, value2100, value2661, value670, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal77 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def boundaryMatrix77 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def boundaryRow77 : Integer.Sparse (Fin 909) := [(0, 5), (1, -73), (2, 44), (3, 160), (4, 64), (5, -15), (7, 20), (8, 40), (10, -36), (12, 56), (13, 32), (23, -120), (24, -336), (27, 123), (30, -192), (55, -192), (79, 36), (80, 72)]

theorem boundarySound77 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow77 (momentVector H) = 0 := by
  have hshape : boundaryMatrix77 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix77 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix77 (0 : Fin 6)) =
      Sparse.eval value2891 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix77 (0 : Fin 6) = raw9164 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9164 hH).trans (sound2891 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix77 (1 : Fin 6)) =
      Sparse.eval value2894 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix77 (1 : Fin 6) = raw9582 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9582 hH).trans (sound2894 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix77 (2 : Fin 6)) =
      Sparse.eval value2894 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix77 (2 : Fin 6) = raw9618 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9618 hH).trans (sound2894 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix77 (3 : Fin 6)) =
      Sparse.eval value2894 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix77 (3 : Fin 6) = raw9639 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9639 hH).trans (sound2894 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix77 (4 : Fin 6)) =
      Sparse.eval value2894 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix77 (4 : Fin 6) = raw9646 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9646 hH).trans (sound2894 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix77 (5 : Fin 6)) =
      Sparse.eval value3453 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix77 (5 : Fin 6) = raw9647 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9647 hH).trans (sound3453 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix77 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix77 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix77 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix77 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix77 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix77 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow77, value2891, value2894, value3453, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal78 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def boundaryMatrix78 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def boundaryRow78 : Integer.Sparse (Fin 909) := [(0, 17), (1, -570), (2, 730), (3, 3040), (4, 1040), (5, -620), (6, 15), (7, 1120), (8, 1760), (12, 400), (23, -480), (24, -1440), (26, 480), (27, 600), (30, -960), (35, 160), (51, -3600), (54, -960), (55, -480), (56, -1920), (77, 720), (78, 1440), (228, -720)]

theorem boundarySound78 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow78 (momentVector H) = 0 := by
  have hshape : boundaryMatrix78 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix78 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix78 (0 : Fin 6)) =
      Sparse.eval value2823 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix78 (0 : Fin 6) = raw9729 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9729 hH).trans (sound2823 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix78 (1 : Fin 6)) =
      Sparse.eval value2889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix78 (1 : Fin 6) = raw9893 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9893 hH).trans (sound2889 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix78 (2 : Fin 6)) =
      Sparse.eval value2889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix78 (2 : Fin 6) = raw9915 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9915 hH).trans (sound2889 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix78 (3 : Fin 6)) =
      Sparse.eval value2887 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix78 (3 : Fin 6) = raw9925 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9925 hH).trans (sound2887 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix78 (4 : Fin 6)) =
      Sparse.eval value2888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix78 (4 : Fin 6) = raw9929 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9929 hH).trans (sound2888 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix78 (5 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix78 (5 : Fin 6) = raw9930 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9930 hH).trans (sound3439 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix78 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix78 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix78 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix78 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix78 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix78 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow78, value2823, value2887, value2888, value2889, value3439, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal79 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def boundaryMatrix79 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def boundaryRow79 : Integer.Sparse (Fin 909) := [(0, -3), (1, 20), (2, 240), (3, 560), (5, -350), (6, 20), (7, 600), (8, 520), (10, -180), (12, 180), (13, 240), (23, -60), (27, 45), (30, -120), (35, 240), (51, -480), (52, 160), (54, -240), (59, -480), (72, 180), (74, 360), (75, 360), (199, -180)]

theorem boundarySound79 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow79 (momentVector H) = 0 := by
  have hshape : boundaryMatrix79 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix79 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix79 (0 : Fin 6)) =
      Sparse.eval value2880 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (0 : Fin 6) = raw3452 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3452 hH).trans (sound2880 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix79 (1 : Fin 6)) =
      Sparse.eval value2878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (1 : Fin 6) = raw7271 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7271 hH).trans (sound2878 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix79 (2 : Fin 6)) =
      Sparse.eval value2878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (2 : Fin 6) = raw7334 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7334 hH).trans (sound2878 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix79 (3 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (3 : Fin 6) = raw7336 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7336 hH).trans (sound3439 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix79 (4 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (4 : Fin 6) = raw7338 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7338 hH).trans (sound3439 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix79 (5 : Fin 6)) =
      Sparse.eval value2888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (5 : Fin 6) = raw7339 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7339 hH).trans (sound2888 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix79 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow79, value2878, value2880, value2888, value3439, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal80 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def boundaryMatrix80 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def boundaryRow80 : Integer.Sparse (Fin 909) := [(0, -14), (1, 260), (2, 1255), (3, 3120), (4, 400), (5, -2280), (6, 205), (7, 3040), (8, 2720), (26, 480), (35, 2240), (52, 2320), (81, -960), (84, 720), (85, 1440), (86, 1440), (228, -720)]

theorem boundarySound80 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow80 (momentVector H) = 0 := by
  have hshape : boundaryMatrix80 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix80 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix80 (0 : Fin 6)) =
      Sparse.eval value2919 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix80 (0 : Fin 6) = raw3372 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3372 hH).trans (sound2919 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix80 (1 : Fin 6)) =
      Sparse.eval value2921 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix80 (1 : Fin 6) = raw7265 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7265 hH).trans (sound2921 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix80 (2 : Fin 6)) =
      Sparse.eval value2913 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix80 (2 : Fin 6) = raw7295 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7295 hH).trans (sound2913 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix80 (3 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix80 (3 : Fin 6) = raw7312 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7312 hH).trans (sound2914 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix80 (4 : Fin 6)) =
      Sparse.eval value3334 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix80 (4 : Fin 6) = raw7316 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7316 hH).trans (sound3334 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix80 (5 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix80 (5 : Fin 6) = raw7317 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7317 hH).trans (sound3441 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix80 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix80 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix80 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix80 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix80 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix80 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow80, value2913, value2914, value2919, value2921, value3334, value3441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal81 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def boundaryMatrix81 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def boundaryRow81 : Integer.Sparse (Fin 909) := [(0, -17), (1, 80), (2, 990), (3, 2880), (4, 320), (5, -1580), (6, 95), (7, 2800), (8, 2640), (10, -720), (12, 400), (13, 640), (24, -480), (27, 180), (30, -240), (35, 1440), (51, -1920), (52, 640), (56, -960), (59, -1920), (73, 720), (74, 720), (75, 720), (76, 1440), (201, -720)]

theorem boundarySound81 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow81 (momentVector H) = 0 := by
  have hshape : boundaryMatrix81 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix81 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix81 (0 : Fin 6)) =
      Sparse.eval value2881 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix81 (0 : Fin 6) = raw3373 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3373 hH).trans (sound2881 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix81 (1 : Fin 6)) =
      Sparse.eval value2879 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix81 (1 : Fin 6) = raw7266 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7266 hH).trans (sound2879 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix81 (2 : Fin 6)) =
      Sparse.eval value2879 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix81 (2 : Fin 6) = raw7296 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7296 hH).trans (sound2879 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix81 (3 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix81 (3 : Fin 6) = raw7313 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7313 hH).trans (sound3439 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix81 (4 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix81 (4 : Fin 6) = raw7318 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7318 hH).trans (sound3439 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix81 (5 : Fin 6)) =
      Sparse.eval value2889 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix81 (5 : Fin 6) = raw7319 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7319 hH).trans (sound2889 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix81 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix81 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix81 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix81 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix81 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix81 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow81, value2879, value2881, value2889, value3439, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal82 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def boundaryMatrix82 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def boundaryRow82 : Integer.Sparse (Fin 909) := [(0, -17), (1, 280), (2, 1440), (3, 3840), (5, -2160), (6, 185), (7, 2480), (8, 2400), (12, 480), (13, 640), (35, 2400), (52, 3200), (73, 720), (75, 1440), (81, -960), (86, 2880), (201, -720)]

theorem boundarySound82 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow82 (momentVector H) = 0 := by
  have hshape : boundaryMatrix82 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix82 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix82 (0 : Fin 6)) =
      Sparse.eval value2935 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix82 (0 : Fin 6) = raw3367 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3367 hH).trans (sound2935 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix82 (1 : Fin 6)) =
      Sparse.eval value2938 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix82 (1 : Fin 6) = raw7260 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7260 hH).trans (sound2938 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix82 (2 : Fin 6)) =
      Sparse.eval value2938 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix82 (2 : Fin 6) = raw7290 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7290 hH).trans (sound2938 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix82 (3 : Fin 6)) =
      Sparse.eval value2928 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix82 (3 : Fin 6) = raw7299 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7299 hH).trans (sound2928 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix82 (4 : Fin 6)) =
      Sparse.eval value3334 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix82 (4 : Fin 6) = raw7300 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7300 hH).trans (sound3334 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix82 (5 : Fin 6)) =
      Sparse.eval value3440 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix82 (5 : Fin 6) = raw7301 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7301 hH).trans (sound3440 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix82 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix82 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix82 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix82 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix82 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix82 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow82, value2928, value2935, value2938, value3334, value3440, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal83 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def boundaryMatrix83 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def boundaryRow83 : Integer.Sparse (Fin 909) := [(0, -3), (1, 10), (2, 950), (3, 3360), (4, 720), (5, -1240), (6, 95), (7, 1520), (8, 1600), (26, 960), (35, 960), (52, 1280), (81, -1920), (83, 720), (85, 2880), (86, 1440), (228, -1440)]

theorem boundarySound83 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow83 (momentVector H) = 0 := by
  have hshape : boundaryMatrix83 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix83 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix83 (0 : Fin 6)) =
      Sparse.eval value2908 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (0 : Fin 6) = raw3368 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3368 hH).trans (sound2908 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix83 (1 : Fin 6)) =
      Sparse.eval value2910 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (1 : Fin 6) = raw7261 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7261 hH).trans (sound2910 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix83 (2 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (2 : Fin 6) = raw7291 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7291 hH).trans (sound2914 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix83 (3 : Fin 6)) =
      Sparse.eval value2910 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (3 : Fin 6) = raw7302 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7302 hH).trans (sound2910 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix83 (4 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (4 : Fin 6) = raw7305 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7305 hH).trans (sound2914 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix83 (5 : Fin 6)) =
      Sparse.eval value3373 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (5 : Fin 6) = raw7306 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7306 hH).trans (sound3373 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix83 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow83, value2908, value2910, value2914, value3373, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal84 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def boundaryMatrix84 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def boundaryRow84 : Integer.Sparse (Fin 909) := [(0, 13), (1, -580), (2, 285), (3, 4800), (4, 800), (5, -100), (7, 560), (8, 160), (10, -240), (12, 1920), (13, 1520), (23, -1920), (24, -1440), (25, -240), (27, 420), (47, 2880), (48, 1440), (50, 720), (51, -1440), (55, -960), (59, -480), (79, 720), (94, 1440)]

theorem boundarySound84 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow84 (momentVector H) = 0 := by
  have hshape : boundaryMatrix84 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix84 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix84 (0 : Fin 6)) =
      Sparse.eval value3089 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix84 (0 : Fin 6) = raw9127 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9127 hH).trans (sound3089 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix84 (1 : Fin 6)) =
      Sparse.eval value2455 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix84 (1 : Fin 6) = raw9395 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9395 hH).trans (sound2455 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix84 (2 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix84 (2 : Fin 6) = raw9457 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9457 hH).trans (sound3090 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix84 (3 : Fin 6)) =
      Sparse.eval value3090 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix84 (3 : Fin 6) = raw9478 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9478 hH).trans (sound3090 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix84 (4 : Fin 6)) =
      Sparse.eval value2944 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix84 (4 : Fin 6) = raw9487 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9487 hH).trans (sound2944 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix84 (5 : Fin 6)) =
      Sparse.eval value3425 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix84 (5 : Fin 6) = raw9488 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9488 hH).trans (sound3425 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix84 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix84 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix84 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix84 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix84 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix84 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow84, value2455, value2944, value3089, value3090, value3425, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
