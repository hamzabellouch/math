import OAI.Analysis.MutuallyUnbiased.Certificate.Integer
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical268
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical269
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical271
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical273

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryOriginal49 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def boundaryMatrix49 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def boundaryRow49 : Integer.Sparse (Fin 909) := [(0, -9), (1, 135), (2, -160), (3, -1280), (4, -480), (5, 260), (6, -30), (7, -720), (8, -240), (9, 20), (24, 720), (26, -480), (35, -640), (52, -480), (69, -240), (70, -160), (71, -80), (126, 720), (197, 480)]

theorem boundarySound49 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow49 (momentVector H) = 0 := by
  have hshape : boundaryMatrix49 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix49 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix49 (0 : Fin 6)) =
      Sparse.eval value2114 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix49 (0 : Fin 6) = raw8180 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8180 hH).trans (sound2114 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix49 (1 : Fin 6)) =
      Sparse.eval value2114 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix49 (1 : Fin 6) = raw8557 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8557 hH).trans (sound2114 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix49 (2 : Fin 6)) =
      Sparse.eval value562 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix49 (2 : Fin 6) = raw8609 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8609 hH).trans (sound562 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix49 (3 : Fin 6)) =
      Sparse.eval value2128 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix49 (3 : Fin 6) = raw8633 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8633 hH).trans (sound2128 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix49 (4 : Fin 6)) =
      Sparse.eval value1876 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix49 (4 : Fin 6) = raw8639 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8639 hH).trans (sound1876 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix49 (5 : Fin 6)) =
      Sparse.eval value2129 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix49 (5 : Fin 6) = raw8640 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8640 hH).trans (sound2129 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix49 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix49 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix49 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix49 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix49 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix49 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow49, value1876, value2114, value2128, value2129, value562, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal50 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def boundaryMatrix50 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def boundaryRow50 : Integer.Sparse (Fin 909) := [(0, 3), (1, 105), (2, -90), (3, -1440), (5, 210), (6, -30), (7, -480), (9, 10), (12, -600), (13, -1240), (23, 360), (35, -720), (52, -480), (54, 720), (69, -120), (70, -120), (125, 360), (196, 240)]

theorem boundarySound50 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow50 (momentVector H) = 0 := by
  have hshape : boundaryMatrix50 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix50 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix50 (0 : Fin 6)) =
      Sparse.eval value2116 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix50 (0 : Fin 6) = raw8187 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8187 hH).trans (sound2116 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix50 (1 : Fin 6)) =
      Sparse.eval value2116 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix50 (1 : Fin 6) = raw8564 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8564 hH).trans (sound2116 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix50 (2 : Fin 6)) =
      Sparse.eval value2132 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix50 (2 : Fin 6) = raw8656 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8656 hH).trans (sound2132 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix50 (3 : Fin 6)) =
      Sparse.eval value2132 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix50 (3 : Fin 6) = raw8663 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8663 hH).trans (sound2132 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix50 (4 : Fin 6)) =
      Sparse.eval value1878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix50 (4 : Fin 6) = raw8668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8668 hH).trans (sound1878 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix50 (5 : Fin 6)) =
      Sparse.eval value2131 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix50 (5 : Fin 6) = raw8669 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8669 hH).trans (sound2131 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix50 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix50 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix50 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix50 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix50 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix50 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow50, value1878, value2116, value2131, value2132, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal51 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def boundaryMatrix51 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def boundaryRow51 : Integer.Sparse (Fin 909) := [(0, -4), (1, 45), (2, -230), (3, -640), (4, -160), (5, 280), (6, -15), (7, -480), (8, -480), (9, 20), (24, 480), (27, -60), (51, 480), (52, -160), (69, -160), (71, -320), (124, 240), (126, 960)]

theorem boundarySound51 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow51 (momentVector H) = 0 := by
  have hshape : boundaryMatrix51 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix51 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix51 (0 : Fin 6)) =
      Sparse.eval value1871 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix51 (0 : Fin 6) = raw8202 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8202 hH).trans (sound1871 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix51 (1 : Fin 6)) =
      Sparse.eval value560 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix51 (1 : Fin 6) = raw8680 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8680 hH).trans (sound560 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix51 (2 : Fin 6)) =
      Sparse.eval value560 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix51 (2 : Fin 6) = raw8706 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8706 hH).trans (sound560 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix51 (3 : Fin 6)) =
      Sparse.eval value1883 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix51 (3 : Fin 6) = raw8726 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8726 hH).trans (sound1883 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix51 (4 : Fin 6)) =
      Sparse.eval value1884 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix51 (4 : Fin 6) = raw8731 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8731 hH).trans (sound1884 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix51 (5 : Fin 6)) =
      Sparse.eval value1538 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix51 (5 : Fin 6) = raw8732 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8732 hH).trans (sound1538 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix51 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix51 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix51 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix51 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix51 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix51 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow51, value1538, value1871, value1883, value1884, value560, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal52 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def boundaryMatrix52 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def boundaryRow52 : Integer.Sparse (Fin 909) := [(0, -14), (1, 65), (2, -250), (3, -320), (5, 440), (6, -45), (7, -160), (8, -800), (9, 20), (27, -60), (30, 480), (52, -160), (69, -80), (71, -400), (126, 240), (236, 960)]

theorem boundarySound52 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow52 (momentVector H) = 0 := by
  have hshape : boundaryMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix52 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix52 (0 : Fin 6)) =
      Sparse.eval value2459 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix52 (0 : Fin 6) = raw6812 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6812 hH).trans (sound2459 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix52 (1 : Fin 6)) =
      Sparse.eval value2459 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix52 (1 : Fin 6) = raw8530 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8530 hH).trans (sound2459 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix52 (2 : Fin 6)) =
      Sparse.eval value2462 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix52 (2 : Fin 6) = raw8577 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8577 hH).trans (sound2462 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix52 (3 : Fin 6)) =
      Sparse.eval value881 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix52 (3 : Fin 6) = raw8620 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8620 hH).trans (sound881 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix52 (4 : Fin 6)) =
      Sparse.eval value1876 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix52 (4 : Fin 6) = raw8639 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8639 hH).trans (sound1876 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix52 (5 : Fin 6)) =
      Sparse.eval value2674 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix52 (5 : Fin 6) = raw8641 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8641 hH).trans (sound2674 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix52 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix52 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix52 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix52 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix52 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix52 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow52, value1876, value2459, value2462, value2674, value881, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal53 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def boundaryMatrix53 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def boundaryRow53 : Integer.Sparse (Fin 909) := [(0, -2), (1, 95), (2, -60), (3, -880), (4, -320), (5, 460), (6, -65), (7, -160), (8, -480), (9, 20), (13, -400), (24, 480), (26, -320), (35, -400), (52, -320), (55, 240), (56, 960), (69, -80), (70, -80), (71, -320), (125, 240), (197, 960)]

theorem boundarySound53 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow53 (momentVector H) = 0 := by
  have hshape : boundaryMatrix53 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix53 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix53 (0 : Fin 6)) =
      Sparse.eval value2649 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix53 (0 : Fin 6) = raw6828 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6828 hH).trans (sound2649 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix53 (1 : Fin 6)) =
      Sparse.eval value2649 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix53 (1 : Fin 6) = raw8536 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8536 hH).trans (sound2649 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix53 (2 : Fin 6)) =
      Sparse.eval value1149 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix53 (2 : Fin 6) = raw8610 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8610 hH).trans (sound1149 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix53 (3 : Fin 6)) =
      Sparse.eval value1149 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix53 (3 : Fin 6) = raw8660 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8660 hH).trans (sound1149 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix53 (4 : Fin 6)) =
      Sparse.eval value1878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix53 (4 : Fin 6) = raw8668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8668 hH).trans (sound1878 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix53 (5 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix53 (5 : Fin 6) = raw8671 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8671 hH).trans (sound2671 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix53 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix53 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix53 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix53 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix53 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix53 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow53, value1149, value1878, value2649, value2671, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal54 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def boundaryMatrix54 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def boundaryRow54 : Integer.Sparse (Fin 909) := [(0, -1), (1, 35), (2, -140), (3, -480), (5, 265), (6, -15), (7, -600), (8, -480), (10, 180), (12, -120), (13, -160), (35, -320), (82, -60)]

theorem boundarySound54 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow54 (momentVector H) = 0 := by
  have hshape : boundaryMatrix54 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix54 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix54 (0 : Fin 6)) =
      Sparse.eval value1543 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix54 (0 : Fin 6) = raw8174 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8174 hH).trans (sound1543 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix54 (1 : Fin 6)) =
      Sparse.eval value1543 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix54 (1 : Fin 6) = raw8550 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8550 hH).trans (sound1543 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix54 (2 : Fin 6)) =
      Sparse.eval value1543 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix54 (2 : Fin 6) = raw8580 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8580 hH).trans (sound1543 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix54 (3 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix54 (3 : Fin 6) = raw8597 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8597 hH).trans (sound1542 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix54 (4 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix54 (4 : Fin 6) = raw8600 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8600 hH).trans (sound1542 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix54 (5 : Fin 6)) =
      Sparse.eval value1891 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix54 (5 : Fin 6) = raw8601 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8601 hH).trans (sound1891 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix54 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix54 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix54 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix54 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix54 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix54 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow54, value1542, value1543, value1891, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal55 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def boundaryMatrix55 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def boundaryRow55 : Integer.Sparse (Fin 909) := [(0, -1), (1, 10), (2, -205), (3, -1200), (4, -240), (5, 680), (6, -90), (7, -480), (8, -480), (11, -240), (26, -480), (35, -1120), (52, -1200), (228, 720)]

theorem boundarySound55 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow55 (momentVector H) = 0 := by
  have hshape : boundaryMatrix55 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix55 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix55 (0 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix55 (0 : Fin 6) = raw6801 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical6801 hH).trans (sound2382 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix55 (1 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix55 (1 : Fin 6) = raw8523 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8523 hH).trans (sound2382 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix55 (2 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix55 (2 : Fin 6) = raw8570 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8570 hH).trans (sound2382 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix55 (3 : Fin 6)) =
      Sparse.eval value2384 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix55 (3 : Fin 6) = raw8585 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8585 hH).trans (sound2384 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix55 (4 : Fin 6)) =
      Sparse.eval value748 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix55 (4 : Fin 6) = raw8596 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8596 hH).trans (sound748 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix55 (5 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix55 (5 : Fin 6) = raw8597 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8597 hH).trans (sound1542 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix55 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix55 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix55 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix55 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix55 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix55 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow55, value1542, value2382, value2384, value748, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal56 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def boundaryMatrix56 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def boundaryRow56 : Integer.Sparse (Fin 909) := [(0, 1), (1, -30), (2, -50), (3, -160), (5, 90), (6, -15), (7, -40), (8, -80), (12, -20), (13, -160), (35, -160), (52, -320), (82, -120), (128, -160), (199, 60), (201, 240)]

theorem boundarySound56 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow56 (momentVector H) = 0 := by
  have hshape : boundaryMatrix56 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix56 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix56 (0 : Fin 6)) =
      Sparse.eval value2134 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix56 (0 : Fin 6) = raw4056 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical4056 hH).trans (sound2134 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix56 (1 : Fin 6)) =
      Sparse.eval value2658 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix56 (1 : Fin 6) = raw7369 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7369 hH).trans (sound2658 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix56 (2 : Fin 6)) =
      Sparse.eval value2658 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix56 (2 : Fin 6) = raw7422 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7422 hH).trans (sound2658 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix56 (3 : Fin 6)) =
      Sparse.eval value2799 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix56 (3 : Fin 6) = raw7430 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7430 hH).trans (sound2799 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix56 (4 : Fin 6)) =
      Sparse.eval value2799 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix56 (4 : Fin 6) = raw7434 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7434 hH).trans (sound2799 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix56 (5 : Fin 6)) =
      Sparse.eval value2380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix56 (5 : Fin 6) = raw7436 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7436 hH).trans (sound2380 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix56 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix56 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix56 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix56 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix56 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix56 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow56, value2134, value2380, value2658, value2799, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal57 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def boundaryMatrix57 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def boundaryRow57 : Integer.Sparse (Fin 909) := [(0, -1), (1, -10), (2, -5), (3, -480), (5, 10), (7, -240), (10, 360), (12, -240), (13, -640), (35, -320), (82, -120), (127, 360), (128, -120)]

theorem boundarySound57 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow57 (momentVector H) = 0 := by
  have hshape : boundaryMatrix57 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix57 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix57 (0 : Fin 6)) =
      Sparse.eval value1881 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix57 (0 : Fin 6) = raw8173 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8173 hH).trans (sound1881 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix57 (1 : Fin 6)) =
      Sparse.eval value1881 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix57 (1 : Fin 6) = raw8549 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8549 hH).trans (sound1881 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix57 (2 : Fin 6)) =
      Sparse.eval value1881 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix57 (2 : Fin 6) = raw8579 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8579 hH).trans (sound1881 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix57 (3 : Fin 6)) =
      Sparse.eval value566 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix57 (3 : Fin 6) = raw8586 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8586 hH).trans (sound566 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix57 (4 : Fin 6)) =
      Sparse.eval value1880 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix57 (4 : Fin 6) = raw8589 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8589 hH).trans (sound1880 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix57 (5 : Fin 6)) =
      Sparse.eval value2135 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix57 (5 : Fin 6) = raw8590 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8590 hH).trans (sound2135 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix57 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix57 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix57 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix57 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix57 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix57 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow57, value1880, value1881, value2135, value566, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal58 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def boundaryMatrix58 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def boundaryRow58 : Integer.Sparse (Fin 909) := [(0, -9), (1, 525), (2, 90), (3, -3360), (4, -1200), (5, 140), (6, -30), (7, -240), (11, -240), (12, -960), (13, -1680), (25, 720), (26, -1440), (35, -1520), (52, -240), (54, 2160), (56, 1440), (226, 480), (228, 720)]

theorem boundarySound58 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow58 (momentVector H) = 0 := by
  have hshape : boundaryMatrix58 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix58 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix58 (0 : Fin 6)) =
      Sparse.eval value2298 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix58 (0 : Fin 6) = raw8185 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8185 hH).trans (sound2298 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix58 (1 : Fin 6)) =
      Sparse.eval value2298 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix58 (1 : Fin 6) = raw8562 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8562 hH).trans (sound2298 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix58 (2 : Fin 6)) =
      Sparse.eval value2296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix58 (2 : Fin 6) = raw8648 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8648 hH).trans (sound2296 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix58 (3 : Fin 6)) =
      Sparse.eval value2297 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix58 (3 : Fin 6) = raw8653 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8653 hH).trans (sound2297 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix58 (4 : Fin 6)) =
      Sparse.eval value2132 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix58 (4 : Fin 6) = raw8656 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8656 hH).trans (sound2132 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix58 (5 : Fin 6)) =
      Sparse.eval value2301 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix58 (5 : Fin 6) = raw8657 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8657 hH).trans (sound2301 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix58 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix58 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix58 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix58 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix58 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix58 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow58, value2132, value2296, value2297, value2298, value2301, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal59 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def boundaryMatrix59 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def boundaryRow59 : Integer.Sparse (Fin 909) := [(0, -19), (1, 270), (2, -105), (3, -1360), (4, -560), (5, 240), (6, -40), (11, -80), (26, -640), (27, -120), (31, 480), (35, -480), (52, -400), (55, 480), (228, 240), (237, 480), (238, 480)]

theorem boundarySound59 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow59 (momentVector H) = 0 := by
  have hshape : boundaryMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix59 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix59 (0 : Fin 6)) =
      Sparse.eval value2472 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix59 (0 : Fin 6) = raw8208 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8208 hH).trans (sound2472 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix59 (1 : Fin 6)) =
      Sparse.eval value872 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix59 (1 : Fin 6) = raw8685 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8685 hH).trans (sound872 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix59 (2 : Fin 6)) =
      Sparse.eval value2470 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix59 (2 : Fin 6) = raw8738 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8738 hH).trans (sound2470 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix59 (3 : Fin 6)) =
      Sparse.eval value2471 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix59 (3 : Fin 6) = raw8749 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8749 hH).trans (sound2471 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix59 (4 : Fin 6)) =
      Sparse.eval value2474 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix59 (4 : Fin 6) = raw8756 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8756 hH).trans (sound2474 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix59 (5 : Fin 6)) =
      Sparse.eval value2669 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix59 (5 : Fin 6) = raw8757 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8757 hH).trans (sound2669 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix59 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix59 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix59 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix59 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix59 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix59 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow59, value2470, value2471, value2472, value2474, value2669, value872, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal60 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def boundaryMatrix60 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def boundaryRow60 : Integer.Sparse (Fin 909) := [(1, 35), (2, -13), (3, -400), (4, -64), (5, 44), (6, -8), (7, -48), (12, -144), (13, -368), (26, -64), (35, -208), (52, -128), (54, 144), (56, 96), (82, -64), (128, -64), (199, 48), (201, 96)]

theorem boundarySound60 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow60 (momentVector H) = 0 := by
  have hshape : boundaryMatrix60 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix60 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix60 (0 : Fin 6)) =
      Sparse.eval value2122 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix60 (0 : Fin 6) = raw8205 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8205 hH).trans (sound2122 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix60 (1 : Fin 6)) =
      Sparse.eval value663 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix60 (1 : Fin 6) = raw8682 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8682 hH).trans (sound663 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix60 (2 : Fin 6)) =
      Sparse.eval value2140 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix60 (2 : Fin 6) = raw8735 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8735 hH).trans (sound2140 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix60 (3 : Fin 6)) =
      Sparse.eval value2140 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix60 (3 : Fin 6) = raw8745 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8745 hH).trans (sound2140 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix60 (4 : Fin 6)) =
      Sparse.eval value1887 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix60 (4 : Fin 6) = raw8747 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8747 hH).trans (sound1887 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix60 (5 : Fin 6)) =
      Sparse.eval value2139 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix60 (5 : Fin 6) = raw8748 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8748 hH).trans (sound2139 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix60 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix60 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix60 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix60 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix60 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix60 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow60, value1887, value2122, value2139, value2140, value663, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal64 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def boundaryMatrix64 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def boundaryRow64 : Integer.Sparse (Fin 909) := [(0, 7), (1, -140), (2, -465), (3, -1680), (5, 1240), (6, -160), (7, -960), (8, -960), (12, -240), (13, -1120), (35, -1520), (52, -1920), (59, 720), (60, -320), (128, -240)]

theorem boundarySound64 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow64 (momentVector H) = 0 := by
  have hshape : boundaryMatrix64 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix64 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix64 (0 : Fin 6)) =
      Sparse.eval value1391 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix64 (0 : Fin 6) = raw3917 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3917 hH).trans (sound1391 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix64 (1 : Fin 6)) =
      Sparse.eval value1391 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix64 (1 : Fin 6) = raw7360 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7360 hH).trans (sound1391 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix64 (2 : Fin 6)) =
      Sparse.eval value1390 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix64 (2 : Fin 6) = raw7379 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7379 hH).trans (sound1390 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix64 (3 : Fin 6)) =
      Sparse.eval value2380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix64 (3 : Fin 6) = raw7382 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7382 hH).trans (sound2380 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix64 (4 : Fin 6)) =
      Sparse.eval value2380 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix64 (4 : Fin 6) = raw7383 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7383 hH).trans (sound2380 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix64 (5 : Fin 6)) =
      Sparse.eval value2791 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix64 (5 : Fin 6) = raw7384 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7384 hH).trans (sound2791 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix64 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix64 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix64 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix64 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix64 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix64 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow64, value1390, value1391, value2380, value2791, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal65 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def boundaryMatrix65 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def boundaryRow65 : Integer.Sparse (Fin 909) := [(0, 1), (1, -5), (2, -120), (3, -480), (4, -80), (5, 240), (6, -20), (7, -480), (8, -320), (26, -160), (35, -400), (52, -160), (67, -80), (81, 240)]

theorem boundarySound65 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow65 (momentVector H) = 0 := by
  have hshape : boundaryMatrix65 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix65 2 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix65 (0 : Fin 6)) =
      Sparse.eval value1529 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix65 (0 : Fin 6) = raw3940 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3940 hH).trans (sound1529 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix65 (1 : Fin 6)) =
      Sparse.eval value1530 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix65 (1 : Fin 6) = raw7361 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7361 hH).trans (sound1530 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix65 (2 : Fin 6)) =
      Sparse.eval value1531 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix65 (2 : Fin 6) = raw7387 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7387 hH).trans (sound1531 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix65 (3 : Fin 6)) =
      Sparse.eval value1531 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix65 (3 : Fin 6) = raw7389 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7389 hH).trans (sound1531 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix65 (4 : Fin 6)) =
      Sparse.eval value1542 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix65 (4 : Fin 6) = raw7390 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7390 hH).trans (sound1542 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix65 (5 : Fin 6)) =
      Sparse.eval value2469 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix65 (5 : Fin 6) = raw7391 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7391 hH).trans (sound2469 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix65 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix65 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix65 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix65 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix65 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix65 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow65, value1529, value1530, value1531, value1542, value2469, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal66 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def boundaryMatrix66 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def boundaryRow66 : Integer.Sparse (Fin 909) := [(0, 12), (1, 50), (2, -15), (3, -1760), (5, 20), (6, -5), (12, -720), (13, -2000), (26, -560), (32, -160), (33, 720), (34, -480), (35, -240), (55, 720), (60, -160), (61, 480)]

theorem boundarySound66 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow66 (momentVector H) = 0 := by
  have hshape : boundaryMatrix66 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix66 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix66 (0 : Fin 6)) =
      Sparse.eval value1435 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix66 (0 : Fin 6) = raw8182 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8182 hH).trans (sound1435 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix66 (1 : Fin 6)) =
      Sparse.eval value1435 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix66 (1 : Fin 6) = raw8559 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8559 hH).trans (sound1435 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix66 (2 : Fin 6)) =
      Sparse.eval value573 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix66 (2 : Fin 6) = raw8612 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8612 hH).trans (sound573 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix66 (3 : Fin 6)) =
      Sparse.eval value1428 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix66 (3 : Fin 6) = raw8636 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8636 hH).trans (sound1428 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix66 (4 : Fin 6)) =
      Sparse.eval value1427 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix66 (4 : Fin 6) = raw8644 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8644 hH).trans (sound1427 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix66 (5 : Fin 6)) =
      Sparse.eval value2793 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix66 (5 : Fin 6) = raw8645 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8645 hH).trans (sound2793 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix66 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix66 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix66 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix66 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix66 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix66 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow66, value1427, value1428, value1435, value2793, value573, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

def boundaryOriginal67 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def boundaryMatrix67 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def boundaryRow67 : Integer.Sparse (Fin 909) := [(0, 2), (1, 6), (2, -5), (3, -256), (5, 8), (6, -1), (12, -96), (13, -224), (25, 48), (26, -64), (33, 192), (34, -32), (35, -32), (52, -32), (55, 96), (63, 48), (64, 96)]

theorem boundarySound67 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow67 (momentVector H) = 0 := by
  have hshape : boundaryMatrix67 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix67 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix67 (0 : Fin 6)) =
      Sparse.eval value1418 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix67 (0 : Fin 6) = raw8203 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8203 hH).trans (sound1418 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix67 (1 : Fin 6)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix67 (1 : Fin 6) = raw8681 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8681 hH).trans (sound868 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix67 (2 : Fin 6)) =
      Sparse.eval value868 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix67 (2 : Fin 6) = raw8707 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8707 hH).trans (sound868 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix67 (3 : Fin 6)) =
      Sparse.eval value1427 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix67 (3 : Fin 6) = raw8727 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8727 hH).trans (sound1427 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix67 (4 : Fin 6)) =
      Sparse.eval value1428 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix67 (4 : Fin 6) = raw8733 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8733 hH).trans (sound1428 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix67 (5 : Fin 6)) =
      Sparse.eval value2790 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix67 (5 : Fin 6) = raw8734 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8734 hH).trans (sound2790 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix67 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix67 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix67 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix67 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix67 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix67 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow67, value1418, value1427, value1428, value2790, value868, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
